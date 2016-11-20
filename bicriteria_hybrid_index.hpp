/*
 * bicriteria_hybrid_index.hpp
 *
 *  Created on: Sep 12, 2016
 *      Author: xsong
 */

#ifndef BICRITERIA_HYBRID_INDEX_HPP_
#define BICRITERIA_HYBRID_INDEX_HPP_

#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <thread>
#include <numeric>
#include <memory>

#include <boost/lexical_cast.hpp>
#include <boost/filesystem/operations.hpp>
#include <boost/serialization/vector.hpp>
#include <boost/archive/binary_iarchive.hpp>
#include <boost/archive/binary_oarchive.hpp>

#include <succinct/mapper.hpp>

#include <stxxl/vector>
#include <stxxl/io>
#include <stxxl/sort>

#include "configuration.hpp"
#include "index_types.hpp"
#include "util.hpp"
#include "verify_collection.hpp"
#include "index_build_utils.hpp"
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

	std::string space_name(double value) {
//		if (value < kilo_num) {
		std::ostringstream ost;
		ost.setf(std::ios::fixed);
		ost.precision(0);
		ost << value << "B";
		return ost.str();
//		} else if (value < mega_num) {
//			return prec_print(value, 8 * kilo_num, 2).append("KB");
//		} else {
//			return prec_print(value, 8 * mega_num, 2).append("MB");
//		}
	}

	std::string time_name(double value) {
//		if (value < std::giga::num) {
		std::ostringstream ost;
		ost << (value / std::mega::num) << "msec";
		return ost.str();
//		} else {
//			return prec_print(value, std::giga::num, 2).append("sec");
//		}
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
	double value = 0;
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

typedef stxxl::vector<lambda_point> lambda_vector_type;

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
		lp_indexs.assign(size, 0);
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

	void save(std::ofstream &out) {
		boost::archive::binary_oarchive oa(out);
		oa & space;
		oa & time;
		oa & BOOST_SERIALIZATION_NVP(lp_indexs);
		out.flush();
		out.close();
	}

	void load(std::ifstream &in) {
		boost::archive::binary_iarchive ia(in);
		ia & space;
		ia & time;
		ia & BOOST_SERIALIZATION_NVP(lp_indexs);
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

		logger() << "buget is set to be " << budget->name() << ", namely "
				<< fix_bound.name() << std::endl;

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

typedef std::unordered_map<block_id_type, std::vector<lambda_point>> block_lambdas_type;

#endif /* BICRITERIA_HYBRID_INDEX_HPP_ */
