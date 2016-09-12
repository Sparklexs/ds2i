/*
 * bicriteria_hybrid_index.cpp
 *
 *  Created on: May 12, 2016
 *      Author: xsong
 */

#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <thread>
#include <numeric>
#include <memory>

#include <boost/lexical_cast.hpp>
#include <boost/filesystem/operations.hpp>

#include <succinct/mapper.hpp>

#include <stxxl/vector>
#include <stxxl/io>
#include <stxxl/sort>

#include "configuration.hpp"
#include "index_types.hpp"
#include "util.hpp"
#include "verify_collection.hpp"
#include "index_build_utils.hpp"
//#define NDEBUG

using ds2i::logger;

typedef uint32_t block_id_type; // XXX for memory reasons, but would need size_t for very large indexes
typedef std::tuple<uint32_t, uint32_t> type_param_pair; // encoder_id, parameter

enum bound_type {
	TIME, SPACE
};

class fixed_bound;

class bound {
	bound_type bt;
public:

	bound(bound_type bt) :
			bt(bt) {

	}

	virtual fixed_bound get_fixed(double max_w, double min_w) = 0;

	bound_type type() {
		return bt;
	}

	virtual std::string name() = 0;

	virtual ~bound() {

	}
};

std::string prec_print(unsigned int num, unsigned int den, unsigned int prec) {
	std::stringstream ss;
	if (num % den == 0) {
		ss << num / den;
	} else {
		ss.precision(prec);
		ss << std::fixed << 1.0 * num / den;
	}
	return ss.str();
}

unsigned int kilo_num = 1024;
unsigned int mega_num = 1048576;

class fixed_bound: public bound {
private:
	// nanoseconds / bytes
	double fix_bound;

	std::string space_name(unsigned int value) {
		if (value < kilo_num) {
			std::ostringstream ost;
			ost << value << "B";
			return ost.str();
		} else if (value < mega_num) {
			return prec_print(value, 8 * kilo_num, 2).append("KB");
		} else {
			return prec_print(value, 8 * mega_num, 2).append("MB");
		}
	}

	std::string time_name(unsigned int value) {
		if (value < std::giga::num) {
			std::ostringstream ost;
			ost << (value / std::mega::num) << "msec";
			return ost.str();
		} else {
			return prec_print(value, std::giga::num, 2).append("sec");
		}
	}

public:
	fixed_bound(bound_type bt, double fix_bound) :
			bound(bt), fix_bound(fix_bound) {

	}

	fixed_bound get_fixed(double, double) {
		return *this;
	}

	double get_bound() {
		return fix_bound;
	}

	std::string name() {
		switch (type()) {
		case SPACE:
			return space_name(fix_bound);
		default:
			return time_name(fix_bound);
		}
	}
};

class relative_bound: public bound {
private:
	double c_level;
public:
	relative_bound(bound_type bt, double c_level) :
			bound(bt), c_level(c_level) {

	}

	fixed_bound get_fixed(double max, double min) {
		return fixed_bound(type(), min + c_level * (max - min));
	}

	std::string name() {
		switch (type()) {
		case SPACE: {
			std::ostringstream ost;
			ost << c_level << "S";
			return ost.str();
		}
		default: {
			std::ostringstream ost;
			ost << c_level << "T";
			return ost.str();
		}
		}
	}
};

std::shared_ptr<bound> add_bound(const char* param) {
	std::string paramstr(param);
	char kind = paramstr.back();
	std::stringstream ss(paramstr.substr(0, paramstr.size() - 1));
	double value = 0.0d;
	ss >> value;
	std::shared_ptr<bound> ptr;
	switch (kind) {
	case 'm': // initial char of 'milliseconds'
		ptr = std::make_shared<fixed_bound>(TIME,
				value * std::nano::den / std::milli::den);
		break;
	case 's': // initial char of 'seconds'
		ptr = std::make_shared<fixed_bound>(TIME, value * std::nano::den);
		break;
	case 'K': // initial char of 'KB'
		ptr = std::make_shared<fixed_bound>(SPACE, 8 * value * kilo_num);
		break;
	case 'M': // initial char of 'MB'
		ptr = std::make_shared<fixed_bound>(SPACE, 8 * value * mega_num);
		break;
	case 'S': // relative bound of S(pace)
		ptr = std::make_shared<relative_bound>(SPACE, value);
		break;
	case 'T': // relative bound of T(ime)
		ptr = std::make_shared<relative_bound>(TIME, value);
		break;
	default:
		throw std::logic_error("No kind specifier in bound");
	}
	return ptr;
}

struct lambda_point {
	block_id_type block_id;
	float lambda;
	ds2i::mixed_block::space_time_point st;

	struct comparator {
		bool operator()(lambda_point const& lhs,
				lambda_point const& rhs) const {
			// in ascending order
			return lhs.lambda < rhs.lambda;
		}

		static lambda_point min_value() {
			lambda_point val;
			val.lambda = std::numeric_limits<float>::min();
			return val;
		}

		static lambda_point max_value() {
			lambda_point val;
			val.lambda = std::numeric_limits<float>::max();
			return val;
		}
	};
};

struct cost_weight {
	double cost;
	double weight;

	std::tuple<double, double> get() const {
		return std::make_tuple(cost, weight);
	}
};

class cw_factory {
private:
	bool space_is_cost;
public:
	cw_factory(bool space_is_cost) :
			space_is_cost(space_is_cost) {

	}
	cw_factory(const cw_factory& cw) {
		space_is_cost = cw.space_is_cost;
	}

	cost_weight get(double space, double time) const {
		if (space_is_cost) {
			return {space, time};
		}
		return {time, space};
	}

//	cost_weight get(const solution_info &si) const {
//		double space, time;
//		std::tie(space, time) = si.get();
//		return get(space, time);
//	}
};

class solution_info {
private:
	size_t space;
	double time;
	// index of encoders chosen for current block
	std::vector<int> lp_indexs;
public:
	solution_info() {
	}

	solution_info(size_t _space, double _time, block_id_type size) :
			space(_space), time(_time) {
		lp_indexs.assign(size * 2, 0);
	}

	// const reference can only call functions that end with const
	// so here get_XXXX functions are invalid
	solution_info(const solution_info &si) {
		space = si.space;
		time = si.time;
		lp_indexs = si.lp_indexs;
	}

	// make_tuple function needs copy functions to be non-const
	solution_info(solution_info &si) {
		space = si.get_space();
		time = si.get_time();
		lp_indexs = si.get_index();
	}

	std::vector<int> &get_index() {
		return lp_indexs;
	}

	size_t &get_space() {
		return space;
	}

	double &get_time() {
		return time;
	}

	solution_info& operator =(solution_info si) {
		time = si.get_time();
		space = si.get_space();
		lp_indexs = si.get_index();
		return *this;
	}
};

class solution_dual {
private:
	//	double time, space;
	double cost, weight;
	double W;
//	solution_info *si;
	// lambda_points_index of blocks in current list
	//	std::vector<int> lp_indexs;
public:
	solution_dual(solution_info &si, double _W, const cw_factory cwf) :
			W(_W) {
//		si = &_si;
//		std::cout << si.get_space() << std::endl;
//		std::cout << si.get_time() << std::endl;
		std::tie(cost, weight) = cwf.get(si.get_space(), si.get_time()).get();
		weight -= W;
	}
//	solution_info get_info() {
//		return *si;
//	}
	double get_cost() {
		return cost;
	}
	double get_weight() {
		return weight;
	}
	double L(double mu) {
		return cost + mu * weight;
	}
	bool does_intersect(solution_dual pi) {
		return this->weight != pi.weight;
	}
	std::tuple<double, double> intersect(solution_dual pi) {
		if (!does_intersect(pi))
			throw std::logic_error("Intersection of parallel paths requested!");
		double mu = (cost - pi.cost) / (pi.weight - weight);
		mu = std::max<double>(0.0, mu);
		double value = L(mu);
		return std::make_tuple(mu, value);
	}
	bool feasible() {
		return weight <= 0;
	}
};

class dual_basis {
private:
	double W;
	solution_info s_pos; // positive
	solution_info s_neg; // negative
	cw_factory cwf;
	double mu;
	double phi;

	void update(solution_info new_info_pos, solution_dual new_pos,
			solution_info new_info_neg, solution_dual new_neg) {
		if (!new_pos.does_intersect(new_neg))
			throw std::logic_error("intersection of parallel paths requested!");
		double new_mu, new_value;
		std::tie(new_mu, new_value) = new_pos.intersect(new_neg);
		if (new_value <= phi) {
			s_pos = new_info_pos;
			s_neg = new_info_neg;
		}
	}

public:
	dual_basis(solution_info &left, solution_info &right,
			std::shared_ptr<bound> budget) :
			s_pos(left), s_neg(right), cwf(budget->type() == TIME), mu(-1), phi(
					-1) {
		double max_weight, min_weight;
		if (budget->type() == TIME) {
			max_weight = std::max(s_pos.get_time(), s_neg.get_time());
			min_weight = std::min(s_pos.get_time(), s_neg.get_time());
		} else {
			max_weight = std::max(s_pos.get_space(), s_neg.get_space());
			min_weight = std::min(s_pos.get_space(), s_neg.get_space());
		}

		auto fix_bound = budget->get_fixed(max_weight, min_weight);
		W = fix_bound.get_bound();

		solution_dual _left(left, W, cwf);
		solution_dual _right(right, W, cwf);

#ifndef NDEBUG
		logger() << "Setting W = " << W << " (" << fix_bound.name() << ")"
				<< std::endl;
#endif

		if (max_weight <= W) {
#ifndef NDEBUG
			logger()
					<< "Early return! cost optimal solution does not exceed weight budget."
					<< std::endl;
#endif
			if (_left.get_weight() == 0)
				s_pos = s_neg = left;
			else
				s_pos = s_neg = right;
			return;

		} else if (W == min_weight) {
#ifndef NDEBUG
			logger()
					<< "Early return! weight optimal solution just equals weight budget."
					<< std::endl;
#endif
			if (_left.feasible())
				s_pos = s_neg = left;
			else
				s_pos = s_neg = right;
			return;
		} else if (W < min_weight) {
			throw std::logic_error(
					"Bound less than weight-optimal solution, problem is unfeasible");
		}

		if (_left.feasible()) {
			s_pos = right;
			s_neg = left;
		} else {
			s_pos = left;
			s_neg = right;
		}
		current();
	}

	std::tuple<double, double> current() {
		solution_dual positive(s_pos, W, cwf);
		solution_dual negative(s_neg, W, cwf);
		std::tie(mu, phi) = positive.intersect(negative);
		return std::make_tuple(mu, phi);
//		return s_pos.intersect(s_neg);
	}
	cw_factory get_cwf() const {
		return cwf;
	}
	double get_W() const {
		return W;
	}
	double get_mu() const {
		return mu;
	}
	double get_phi() const {
		return phi;
	}
	std::tuple<double, double> update(solution_info si_candidate) {
		solution_dual sd_candidate(si_candidate, W, cwf);
		if (sd_candidate.feasible()) {
			solution_dual positive(s_pos, W, cwf);
			update(s_pos, positive, si_candidate, sd_candidate);
		} else {
			solution_dual negative(s_neg, W, cwf);
			update(si_candidate, sd_candidate, s_neg, negative);
		}
		return current();
	}
	std::tuple<solution_info, solution_info> get_basis() {
		return std::make_tuple(s_pos, s_neg);
	}

};

std::ostream& print_solution(solution_info& si) {
	return ds2i::logger() << "current solution: S = " << si.get_space()
			<< " bytes, T = " << si.get_time() << " nanoseconds" << std::endl;
}

std::ostream& print_basis(dual_basis &basis) {
	return ds2i::logger() << "mu = " << basis.get_mu() << ",phi = "
			<< basis.get_phi() << std::endl;
}

/*
 *
 */
template<typename InputCollectionType, typename CollectionBuilder>
struct space_time_computer: ds2i::semiasync_queue::job {
	space_time_computer(CollectionBuilder &b,
			typename InputCollectionType::document_enumerator e,
			ds2i::predictors_vec_type const& predictors,
			std::vector<uint32_t>& counts, ds2i::progress_logger& plog,
			std::shared_ptr<bound> budget,
			std::map<type_param_pair, size_t>& t_counts, bool write_to_file,
			size_t& t_space, double& t_time) :
			m_b(b), m_e(e), m_predictors(predictors), m_plog(plog), m_budget(
					budget), m_real_compress(write_to_file), m_type_counts(
					t_counts), m_total_space(t_space), m_total_time(t_time) {
		m_block_access_counts.swap(counts);
//		m_cwf = new cw_factory(budget->type() == TIME);
	}

	virtual void prepare() {
		using namespace ds2i;
		using namespace time_prediction;

		auto blocks = m_e.get_blocks();
		assert(
				m_block_access_counts.empty()
						|| m_block_access_counts.size() == 2 * blocks.size());

		bool heuristic_greedy = configuration::get().heuristic_greedy;

		for (auto const& input_block : blocks) {
			static const uint32_t smoothing = 1;
			uint32_t docs_exp = smoothing, freqs_exp = smoothing;
			if (!m_block_access_counts.empty()) {
				docs_exp += m_block_access_counts[2 * input_block.index];
				freqs_exp += m_block_access_counts[2 * input_block.index + 1];
			}
			thread_local std::vector<uint32_t> values;

			// NOTE, here only defines an anonymous function
			auto append_lambdas =
					[&](std::vector<mixed_block::space_time_point>& points,
							block_id_type block_id, std::map<block_id_type, std::vector<lambda_point>>& m_points_buf) {
						// sort by space, time
						std::sort(points.begin(), points.end());

						// smallest point is always added with lambda=0
						// thus m_points_buf wiill never be cleared
						m_points_buf[block_id].push_back(lambda_point {block_id, 0, points.front()});
						for (auto const& cur: points) {
							while (true) {
								auto const& prev = m_points_buf[block_id].back();
								// if this point is dominated we can skip it
								if (cur.time >= prev.st.time) break;
								// the smaller lambda is, the better the encoder is
								auto lambda = (cur.space - prev.st.space) / (prev.st.time - cur.time);
								// heuristic_greedy is true, then m_points_buf will never kick out lambdas
								// on the other hand, when it is false (as default),points that are dominated
								// will be popped out
								// namely, each time a new point is calculated, it will kick out pointed that
								// are dominated by it
								if (!heuristic_greedy && lambda < prev.lambda) {
									m_points_buf[block_id].pop_back();
								} else {
									m_points_buf[block_id].push_back(lambda_point {block_id, lambda, cur});
									break;
								}
							}
						}
					};

			input_block.decode_doc_gaps(values);
			auto docs_sts = mixed_block::compute_space_time(values,
					input_block.doc_gaps_universe, m_predictors, docs_exp);
			append_lambdas(docs_sts, input_block.index, m_block_doc_lambdas);

			input_block.decode_freqs(values);
			auto freqs_sts = mixed_block::compute_space_time(values,
					uint32_t(-1), m_predictors, freqs_exp);
			append_lambdas(freqs_sts, input_block.index, m_block_freq_lambdas);
		}
		succinct::util::dispose(m_block_access_counts);

#ifndef NDEBUG
		logger() << "now we have calculated all the lambdas for "
				<< blocks.size() << " * 2 blocks in current list." << std::endl;
#endif
		// space-optimal and time-optimal
		/*****************************************************
		 * step 1: initialize two extreme paths as pi_l and pi_r
		 ****************************************************/

		dual_basis basis = initializeSpaceTimeSolutions();

#ifndef NDEBUG
		print_basis(basis);
#endif

		if (basis.get_mu() < 0) {
			// early return found! we will skip following steps and compress immediately.
			std::tie(m_sol_final, m_sol_final) = basis.get_basis();
		} else {
			// next optimize the basis to squeeze the range between
			// UB and LB
			/*****************************************************
			 * step 2: recursively intersect pi_l and pi_r to approximate the boundary
			 ****************************************************/
			optimal(basis);

			//next swap UB and LB if needed
			/*****************************************************
			 * step 3: combine UB and LB into one path
			 ****************************************************/
			m_sol_final = swap_path(basis);

		}

		// transform the compressed data
		/*****************************************************
		 * step 4: recompress all the blocks and flush into disk
		 ****************************************************/

		if (m_real_compress) {
			typedef typename InputCollectionType::document_enumerator::block_data input_block_type;
			typedef mixed_block::block_transformer<input_block_type> output_block_type;

			std::vector<output_block_type> blocks_to_transform;
			for (int i = 0; i < blocks.size(); i++) {
				blocks_to_transform.emplace_back(blocks[i],
						m_block_doc_lambdas[i][m_sol_final.get_index()[2 * i]].st.type,
						m_block_freq_lambdas[i][m_sol_final.get_index()[2 * i
								+ 1]].st.type,
						m_block_doc_lambdas[i][m_sol_final.get_index()[2 * i]].st.param,
						m_block_freq_lambdas[i][m_sol_final.get_index()[2 * i
								+ 1]].st.param);
			}

			block_posting_list<mixed_block>::write_blocks(m_buf, m_e.size(),
					blocks_to_transform);
		}

	}

	virtual void commit() {
		if (m_real_compress) {
			m_b.add_posting_list(m_buf);
			m_plog.done_sequence(m_e.size());
		} else {
			for (int i = 0; i < m_sol_final.get_index().size() / 2; i++) {
				m_type_counts[type_param_pair(
						(uint8_t) m_block_doc_lambdas[i][m_sol_final.get_index()[2
								* i]].st.type,
						m_block_doc_lambdas[i][m_sol_final.get_index()[2 * i]].st.param)] +=
						1;
				m_type_counts[type_param_pair(
						(uint8_t) m_block_doc_lambdas[i][m_sol_final.get_index()[2
								* i + 1]].st.type,
						m_block_doc_lambdas[i][m_sol_final.get_index()[2 * i + 1]].st.param)] +=
						1;
			}
			m_total_space += m_sol_final.get_space();
			m_total_time += m_sol_final.get_time();
			m_plog.done_sequence(m_e.size());
		}
	}

	virtual ~space_time_computer() {
	}

	dual_basis initializeSpaceTimeSolutions() {
		solution_info sol_info_space(m_total_space, m_total_time,
				m_block_doc_lambdas.size());
		solution_info sol_info_time(m_total_space, m_total_time,
				m_block_doc_lambdas.size());
		for (int i = 0; i < m_block_doc_lambdas.size(); i++) {
			// overall space
			sol_info_space.get_space() +=
					m_block_doc_lambdas[i].begin()->st.space;
			sol_info_space.get_space() +=
					m_block_freq_lambdas[i].begin()->st.space;
			// overall time
			sol_info_space.get_time() +=
					m_block_doc_lambdas[i].begin()->st.time;
			sol_info_space.get_time() +=
					m_block_freq_lambdas[i].begin()->st.time;
			// indexes are 0s

			// TODO: something goes wrong when using end() reference
			// it seems end() points to an invalid element rather than
			// the last element with the index of size()-1

			// overall space
			//			sol_info_time.get_space() += m_block_doc_lambdas[i].end()->st.space;
			//			sol_info_time.get_space() +=
			//					m_block_freq_lambdas[i].end()->st.space;

			sol_info_time.get_space() += m_block_doc_lambdas[i].back().st.space;
			sol_info_time.get_space() +=
					m_block_freq_lambdas[i].back().st.space;
			// overall time
			//			sol_info_time.get_time() += m_block_doc_lambdas[i].end()->st.time;
			//			sol_info_time.get_time() += m_block_freq_lambdas[i].end()->st.time;
			sol_info_time.get_time() += m_block_doc_lambdas[i].back().st.time;
			sol_info_time.get_time() += m_block_freq_lambdas[i].back().st.time;
			//indexes are end of each vector
			sol_info_time.get_index()[i * 2] = m_block_doc_lambdas[i].size()
					- 1;
			sol_info_time.get_index()[i * 2 + 1] =
					m_block_freq_lambdas[i].size() - 1;
		}
#ifndef NDEBUG
		logger() << "space-optimal solution: S = " << sol_info_space.get_space()
				<< " bytes, T = " << sol_info_space.get_time() << " nanoseconds"
				<< std::endl;
		logger() << "time-optimal solution: S = " << sol_info_time.get_space()
				<< " bytes, T = " << sol_info_time.get_time() << " nanoseconds"
				<< std::endl;
#endif
		return dual_basis(sol_info_time, sol_info_space, m_budget);
	}

	/*
	 * @brief calculate an upper bound(UB) and a lower bound(LB) on the
	 * optimal value f* for current blocks.
	 *
	 * @param basis structure that contains two paths and current intersection
	 */
	void optimal(dual_basis & basis) {
		const double EPS = 1e-6;
		double phi, phi_pre, delta;

		do {
			phi_pre = basis.get_phi();
			solution_info sol_si(m_total_space, m_total_time,
					m_block_freq_lambdas.size());
			double threshold = 0;
			switch (m_budget->type()) {
			case TIME: //time is weight
				threshold = basis.get_mu();
				break;
			case SPACE: // space is weight
				threshold = 1 / basis.get_mu();
				break;
			}

			// find proper encoding types according to threshold, minimize
			// the overall phi
			for (int i = 0; i < m_block_freq_lambdas.size(); i++) {
//				std::cout << i << ": ";
				int j = 0;
				while (j < m_block_doc_lambdas[i].size()
						&& m_block_doc_lambdas[i][j].lambda < threshold)
					j++;

				j = std::max(0, j - 1);

				sol_si.get_space() += m_block_doc_lambdas[i][j].st.space;
				sol_si.get_time() += m_block_doc_lambdas[i][j].st.time;
				sol_si.get_index()[i * 2] = j;
				j = 0;
				while (j < m_block_freq_lambdas[i].size()
						&& m_block_freq_lambdas[i][j].lambda < threshold)
					j++;
				j = std::max(0, j - 1);

				sol_si.get_space() += m_block_freq_lambdas[i][j].st.space;
				sol_si.get_time() += m_block_freq_lambdas[i][j].st.time;
				//				std::cout<<sol_si.get_space()<<", "<<sol_si.get_time()<<std::endl;
				sol_si.get_index()[i * 2 + 1] = j;
			}

			basis.update(sol_si);
			phi = basis.get_phi();
			delta = std::abs(phi - phi_pre) / phi_pre;
#ifndef NDEBUG
			print_solution(sol_si);
			print_basis(basis);
#endif
		} while (delta > EPS);

		//now we have UB and LB
	}

	solution_info swap_path(dual_basis & basis) {
		solution_info s_1, s_2;
		std::tie(s_1, s_2) = basis.get_basis();
		double W = basis.get_W();

		// early return since the positive path satisfy budget
		if (basis.get_cwf().get(s_1.get_space(), s_1.get_time()).weight <= W)
			return s_1;

		std::array<std::vector<int>::iterator, 2> sol_its = {
				s_1.get_index().begin(), s_2.get_index().begin() };

		std::array<std::map<block_id_type, std::vector<lambda_point>>::iterator,
				2> blocks_its = { m_block_doc_lambdas.begin(),
				m_block_freq_lambdas.begin() };

		unsigned int swap_sol, swap_point;
		swap_sol = swap_point = std::numeric_limits<unsigned int>::max();
		double best_cost = std::numeric_limits<double>::max();

		std::array<size_t, 2> head_spaces { { m_total_space, m_total_space } },
				tail_spaces { { s_1.get_space(), s_2.get_space() } };
		std::array<double, 2> head_times { { m_total_time, m_total_time } },
				tail_times { { s_1.get_time(), s_2.get_time() } };

		size_t count = 0;
		while (sol_its[0] != s_1.get_index().end()
				&& sol_its[1] != s_2.get_index().end()) {

			// 1. skip over blocks using same encoding parameters

			// after this while-loop, head contains blocks[0, the first not equal)
			// tail contains [the first not equal, end].
			// here we do not use do-while loop because head&tail operations are
			// the same for both [0] and [1].
			// so we have to update them after we found non-equivalent blocks.
			while (sol_its[0] != s_1.get_index().end()
					&& *sol_its[0] == *sol_its[1]) {
//				std::cout << "i = " << count << std::endl;
//				std::cout << "block_id = " << (*blocks_its[count % 2]).first
//						<< std::endl;
//				std::cout << "solution type = " << *sol_its[0] << std::endl;
				head_spaces[0] += (*blocks_its[count % 2]).second.at(
						*sol_its[0]).st.space;
				head_times[0] +=
						(*blocks_its[count % 2]).second.at(*sol_its[0]).st.time;
				tail_spaces[0] -= (*blocks_its[count % 2]).second.at(
						*sol_its[0]).st.space;
				tail_times[0] -= (*blocks_its[count++ % 2]++).second.at(
						*sol_its[0]++).st.time;
				// whether equal or not,block 0 has already been swapped.
				*sol_its[1]++;
			}
			if (sol_its[0] == s_1.get_index().end())
				break;
			if (count != 0) {
				head_spaces[1] = head_spaces[0];
				head_times[1] = head_times[0];
				tail_spaces[1] -= head_spaces[1];
				tail_times[1] -= head_times[1];
			}
			// transfer the non-equivalent blocks from tail to head
			for (int i = 0; i < 2; i++) {
				head_spaces[i] += (*blocks_its[count % 2]).second.at(
						*sol_its[i]).st.space;
				head_times[i] +=
						(*blocks_its[count % 2]).second.at(*sol_its[i]).st.time;
				tail_spaces[i] -= (*blocks_its[count % 2]).second.at(
						*sol_its[i]).st.space;
				tail_times[i] -= (*blocks_its[count % 2]).second.at(
						*sol_its[i]++).st.time;
			}
			*blocks_its[count++ % 2]++;

			// 2. try to swap blocks to get better tradeoffs
			// try different combinations of (head,tail)
			for (int j = 0; j < 2; j++) {
				auto s_space = head_spaces[j] + tail_spaces[(j + 1) % 2];
				auto s_time = head_times[j] + tail_times[(j + 1) % 2];
				cost_weight cw = basis.get_cwf().get(s_space, s_time);
				if (cw.weight <= W && cw.cost < best_cost) {
					best_cost = cw.cost;
					swap_point = count - 1;	// where swap position really happens
					swap_sol = j;
				}
			}
		}
#ifndef NDEBUG
		std::cout << "swap starts from " << swap_sol << ", at position "
		<< swap_point << ", with cost " << best_cost << std::endl;
#endif
		if (best_cost < std::numeric_limits<double>::max()) {
			if (swap_sol == 0) {
				std::swap_ranges(s_1.get_index().begin() + swap_point,
						s_1.get_index().end(),
						s_2.get_index().begin() + swap_point);
				return s_1;
			} else {
				std::swap_ranges(s_2.get_index().begin() + swap_point,
						s_2.get_index().end(),
						s_1.get_index().begin() + swap_point);
				return s_2;
			}
		}
		return s_2;
	}

	CollectionBuilder& m_b;
	typename InputCollectionType::document_enumerator m_e;
	ds2i::predictors_vec_type const& m_predictors;
	std::vector<uint32_t> m_block_access_counts;
	ds2i::progress_logger& m_plog;
	std::map<block_id_type, std::vector<lambda_point>> m_block_doc_lambdas;
	std::map<block_id_type, std::vector<lambda_point>> m_block_freq_lambdas;
	std::shared_ptr<bound> m_budget;
	std::vector<uint8_t> m_buf;bool m_real_compress;
	solution_info m_sol_final;

	std::map<type_param_pair, size_t>& m_type_counts;
	size_t& m_total_space;
	double& m_total_time;
//	cw_factory* m_cwf;
}
;

/*
 * compute lambdas and compress in parallel for each posting list
 */
template<typename InputCollectionType>
void compute_solution(InputCollectionType const& input_coll,
		ds2i::global_parameters const& params, size_t space_base,
		const char* predictors_filename, const char* block_stats_filename,
		const char*output_filename, std::shared_ptr<bound> budget) {
	using namespace ds2i;
	using namespace time_prediction;

	logger() << "computing space_time points" << std::endl;
	progress_logger plog;

	auto predictors = load_predictors(predictors_filename);
	std::ifstream block_stats(block_stats_filename);

	double tick = get_time_usecs();
	double user_tick = get_user_time_usecs();

	uint32_t block_counts_list; // termID of current list
	std::vector<uint32_t> block_counts; // doc&freq block counts
	bool block_counts_consumed = true;
	bool write_to_file = false;
	size_t posting_zero_lists = 0;
	size_t posting_zero_blocks = 0;
	semiasync_queue queue(1 << 24);

	if (output_filename)
		write_to_file = true;

	////////////////////////////////////////////////////////////
	typedef typename block_mixed_index::builder builder_type;
	builder_type builder(input_coll.num_docs(), params);
	std::map<type_param_pair, size_t> type_counts;
	double total_time = 0;
	size_t total_space = space_base;
	///////////////////////////////////////////////////////////

	for (size_t l = 0; l < input_coll.size(); l++) {
		if (block_counts_consumed) {
			block_counts_consumed = false;
			read_block_stats(block_stats, block_counts_list, block_counts);
		}

		auto e = input_coll[l];
		typedef space_time_computer<InputCollectionType, builder_type> job_type;
		std::shared_ptr<job_type> job;

		if (l == block_counts_list) {
			posting_zero_blocks += std::accumulate(block_counts.begin(),
					block_counts.end(), size_t(0),
					[](size_t accum, uint32_t freq) {
						return accum+(freq==0);
					});
			block_counts_consumed = true;
			job.reset(
					new job_type(builder, e, predictors, block_counts, plog,
							budget, type_counts, write_to_file, total_space,
							total_time));
		} else {
			posting_zero_lists += 1;
			posting_zero_blocks += 2 * e.num_blocks();
			std::vector<uint32_t> empty_counts;
			job.reset(
					new job_type(builder, e, predictors, empty_counts, plog,
							budget, type_counts, write_to_file, total_space,
							total_time));
		}
		queue.add_job(job, 2 * e.size());
	}

	stats_line()("posting_zero_lists", posting_zero_lists)(
			"posting_zero_blocks", posting_zero_blocks);

	queue.complete();
	plog.log();

	if (write_to_file) {
		///write out the compressed lists into coll
		block_mixed_index coll;
		builder.build(coll);

//		dump_stats(coll, "block_mixed", plog.postings);

		succinct::mapper::freeze(coll, output_filename);
	} else {
		std::vector<std::pair<type_param_pair, size_t>> type_counts_vec;
		for (uint8_t t = 0; t < mixed_block::block_types; ++t) {
			for (uint8_t param = 0;
					param
							< mixed_block::compr_params(
									(mixed_block::block_type) t); ++param) {
				auto tp = type_param_pair(t, param);
				type_counts_vec.push_back(std::make_pair(tp, type_counts[tp]));
			}
		}
		stats_line()("type_counts", type_counts_vec)("total space", total_space)(
				"total time", total_time);
	}

	double elapsed_secs = (get_time_usecs() - tick) / 1000000;
	double user_elapsed_secs = (get_user_time_usecs() - user_tick) / 1000000;

	logger() << "computation finished!" << std::endl;

	stats_line()("worker_threads", configuration::get().worker_threads)(
			"computation_time", elapsed_secs)("computation_user_time",
			user_elapsed_secs)("is_heuristic",
			configuration::get().heuristic_greedy);
}

template<typename InputCollectionType>
void bicriteria_hybrid_index(ds2i::global_parameters const& params,
		const char* predictors_filename, const char* block_stats_filename,
		const char* input_filename, const char* output_filename,
		std::shared_ptr<bound> budget) {
	using namespace ds2i;

	InputCollectionType input_coll;
	boost::iostreams::mapped_file_source m(input_filename);
	succinct::mapper::map(input_coll, m);

	// do some statistics like counting blocks and space cost of auxiliary info
	logger() << "Processing " << input_coll.size() << " posting lists"
			<< std::endl;

	size_t num_blocks = 0;
	size_t partial_blocks = 0;
	size_t space_base = 8; // space overhead independent of block compression method
	for (size_t l = 0; l < input_coll.size(); ++l) {
		auto e = input_coll[l]; // e should be block_posting_list
		num_blocks += 2 * e.num_blocks();
		// (list length) in vbyte, not the compressed size of the whole list
		space_base += succinct::util::ceil_div(
				succinct::broadword::msb(e.size()) + 1, 7);
		space_base += e.num_blocks() * 4; // max docid
		space_base += (e.num_blocks() - 1) * 4; // endpoint
		if (e.size() % mixed_block::block_size != 0) {
			partial_blocks += 2; // docid and freq
		}
	}
	logger() << num_blocks << " overall blocks" << std::endl;
	logger() << partial_blocks << " partial blocks" << std::endl;
	logger() << space_base << " bytes (not including compressed blocks)"
			<< std::endl;

	/*****************************************************
	 * call the function that build the mixed-index
	 ****************************************************/

	compute_solution(input_coll, params, space_base, predictors_filename,
			block_stats_filename, output_filename, budget);

}

int main(int argc, const char** argv) {

	using namespace ds2i;

	if (argc < 5) {
		std::cerr << "Usage: " << argv[0]
				<< " <index type> <predictors> <block_stats> <input_index> <budget> [output_index] [--check <collection_basename>]"
				<< std::endl;
		return 1;
	}

	std::string type = argv[1];
	const char* predictors_filename = argv[2];
	const char* block_stats_filename = argv[3];
	const char* input_filename = argv[4];
//	const char* lambdas_filename = argv[5];
//	size_t budget = boost::lexical_cast<size_t>(argv[6]);

	std::shared_ptr<bound> budget = add_bound(argv[5]);

	const char* output_filename = nullptr;
	if (argc > 6) {
		output_filename = argv[6];
	}

	bool check = false;
	const char* collection_basename = nullptr;
	if (argc > 8 && std::string(argv[7]) == "--check") {
		check = true;
		collection_basename = argv[8];
	}

	ds2i::global_parameters params;

	if (false) {
#define LOOP_BODY(R, DATA, T)                                           \
        } else if (type == BOOST_PP_STRINGIZE(T)) {                     \
            bicriteria_hybrid_index<BOOST_PP_CAT(T, _index)>               \
                (params, predictors_filename, block_stats_filename,     \
                 input_filename, output_filename,  budget); \
            if (check) {                                                \
                binary_freq_collection input(collection_basename);      \
                verify_collection<binary_freq_collection, block_mixed_index> \
                                  (input, output_filename);             \
            }                                                           \
            /**/

	BOOST_PP_SEQ_FOR_EACH(LOOP_BODY, _, DS2I_BLOCK_INDEX_TYPES) ;
#undef LOOP_BODY
	} else {
		logger() << "ERROR: Unknown type " << type << std::endl;
	}

	return 0;
}
