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
#include "bicriteria_hybrid_index.hpp"

dual_basis initializeSpaceTimeSolutions(
		block_lambdas_type& block_doc_freq_lambdas,
		std::shared_ptr<bound> budget, size_t space_base, double time_base) {
	solution_info sol_info_space(space_base, time_base,
			block_doc_freq_lambdas.size());
	solution_info sol_info_time(space_base, time_base,
			block_doc_freq_lambdas.size());

	for (block_lambdas_type::iterator it = block_doc_freq_lambdas.begin();
			it != block_doc_freq_lambdas.end(); it++) {
		// here only needs to traverse all the block_lambdas without
		// considering the order

		// overall space
		sol_info_space.get_space() += it->second.front().st.space;
		sol_info_time.get_space() += it->second.back().st.space;
		// overall time
		sol_info_space.get_time() += it->second.front().st.time;
		sol_info_time.get_time() += it->second.back().st.time;
		// indexes are naturally 0s and size()-1
		sol_info_time.get_index().push_back(block_doc_freq_lambdas.size() - 1);

	}
#ifndef NDEBUG
	logger() << "space-optimal solution: S = " << sol_info_space.get_space()
			<< " bytes, T = " << sol_info_space.get_time() << " nanoseconds"
			<< std::endl;
	logger() << "time-optimal solution: S = " << sol_info_time.get_space()
			<< " bytes, T = " << sol_info_time.get_time() << " nanoseconds"
			<< std::endl;
#endif
	return dual_basis(sol_info_time, sol_info_space, budget);
}

/*
 * @brief calculate an upper bound(UB) and a lower bound(LB) on the
 * optimal value f* for current blocks.
 *
 * @param basis structure that contains two paths and current intersection
 */
void optimize(dual_basis & basis, block_lambdas_type& block_doc_freq_lambdas,
		std::shared_ptr<bound> budget, size_t space_base, double time_base) {
	const double EPS = 1e-6;
	double phi, phi_pre, delta;

	do {
		phi_pre = basis.get_phi();
		solution_info sol_si(space_base, time_base,
				block_doc_freq_lambdas.size());
		double threshold = 0;
		switch (budget->type()) {
		case TIME: //time is weight
			threshold = basis.get_mu();
			break;
		case SPACE: // space is weight
			threshold = 1 / basis.get_mu();
			break;
		}

		// find proper encoding types according to threshold, minimize
		// the overall phi
		for (block_lambdas_type::iterator it = block_doc_freq_lambdas.begin();
				it != block_doc_freq_lambdas.end(); it++) {
			block_id_type j = 0;
			while (j < it->second.size() && it->second[j].lambda < threshold)
				j++;
			j = std::max((block_id_type) 0, j - 1);
			sol_si.get_space() += it->second[j].st.space;
			sol_si.get_time() += it->second[j].st.time;
			//here indexes of solution are assigned according to the blockID
			sol_si.get_index()[it->first] = j;
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

solution_info swapPath(dual_basis & basis,
		block_lambdas_type& block_doc_freq_lambdas, size_t space_base,
		double time_base) {
	solution_info s_1, s_2;
	std::tie(s_1, s_2) = basis.get_basis();
	double W = basis.get_W();

	// early return since the negative path satisfy budget
	if (basis.get_cwf().get(s_2.get_space(), s_2.get_time()).weight <= W)
		return s_2;

	std::array<std::vector<int>::iterator, 2> sol_its = {
			s_1.get_index().begin(), s_2.get_index().begin() };

	unsigned int swap_sol, swap_point;
	swap_sol = swap_point = std::numeric_limits<unsigned int>::max();
	double best_cost = std::numeric_limits<double>::max();

	std::array<size_t, 2> head_spaces { { space_base, space_base } },
			tail_spaces { { s_1.get_space(), s_2.get_space() } };
	std::array<double, 2> head_times { { time_base, time_base } }, tail_times {
			{ s_1.get_time(), s_2.get_time() } };

	while (sol_its[0] != s_1.get_index().end()
			&& sol_its[1] != s_2.get_index().end()) {

		static unsigned int count = 0;
		// 1. skip over blocks using same encoding parameters

		// after this while-loop, head contains blocks[0, the first not equal)
		// tail contains [the first not equal, end].
		// here we do not use do-while loop because head&tail operations are
		// the same for both [0] and [1].
		// so we have to update them after we found non-equivalent blocks.
		while (sol_its[0] != s_1.get_index().end() && *sol_its[0] == *sol_its[1]) {
//				std::cout << "i = " << count << std::endl;
//				std::cout << "block_id = " << (*blocks_its[count % 2]).first
//						<< std::endl;
//				std::cout << "solution type = " << *sol_its[0] << std::endl;

			head_spaces[0] +=
					block_doc_freq_lambdas[count][*sol_its[0]].st.space;
			head_times[0] += block_doc_freq_lambdas[count][*sol_its[0]].st.time;
			tail_spaces[0] -=
					block_doc_freq_lambdas[count][*sol_its[0]].st.space;
			tail_times[0] -=
					block_doc_freq_lambdas[count++][*sol_its[0]++].st.time;
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

			head_spaces[i] +=
					block_doc_freq_lambdas[count][*sol_its[i]].st.space;
			head_times[i] += block_doc_freq_lambdas[count][*sol_its[i]].st.time;

			tail_spaces[i] -=
					block_doc_freq_lambdas[count][*sol_its[i]].st.space;
			tail_times[i] -=
					block_doc_freq_lambdas[count][*sol_its[i]++].st.time;
		}
		// the unequal block has been passed, note only one block
		count++;

		// 2. try to swap blocks to get better tradeoffs
		// try different combinations of (head,tail)
		for (bool j = 0; j < 2; j++) {
			auto s_space = head_spaces[j] + tail_spaces[!j];
			auto s_time = head_times[j] + tail_times[!j];
			cost_weight cw = basis.get_cwf().get(s_space, s_time);
			if (cw.weight <= W && cw.cost < best_cost) {
				best_cost = cw.cost;
				swap_point = count - 1;	// where swap position really happens
				swap_sol = (size_t) j;
			}
		}
	}

#ifndef NDEBUG
	logger() << "swap starts from " << swap_sol << ", at position "
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

template<typename InputCollectionType, typename CollectionBuilder>
struct list_transformer: ds2i::semiasync_queue::job {
	list_transformer(CollectionBuilder& b,
			typename InputCollectionType::document_enumerator e,
			block_lambdas_type & block_doc_freq_lambdas,
			block_id_type block_id_base, std::vector<int>::iterator index_it,
			ds2i::progress_logger& plog) :
			m_b(b), m_e(e), lambdas(block_doc_freq_lambdas), it(index_it), base(
					block_id_base), m_plog(plog) {
	}

	virtual void prepare() {
		using namespace ds2i;

		typedef typename InputCollectionType::document_enumerator::block_data input_block_type;
		typedef mixed_block::block_transformer<input_block_type> output_block_type;

		auto blocks = m_e.get_blocks();
		std::vector<output_block_type> blocks_to_transform;

		for (auto const& input_block : blocks) {

			auto docs_type = lambdas[base][*it].st.type;
			auto docs_param = lambdas[base++][*it++].st.param;
			auto freqs_type = lambdas[base][*it].st.type;
			auto freqs_param = lambdas[base++][*it++].st.param;
			blocks_to_transform.emplace_back(input_block, docs_type, freqs_type,
					docs_param, freqs_param);
		}

		block_posting_list<mixed_block>::write_blocks(m_buf, m_e.size(),
				blocks_to_transform);
	}

	virtual void commit() {
		m_b.add_posting_list(m_buf);
		m_plog.done_sequence(m_e.size());
	}
	virtual ~list_transformer() {
	}

	CollectionBuilder& m_b;
	typename InputCollectionType::document_enumerator m_e;
	block_lambdas_type & lambdas;
	std::vector<int>::iterator it;
	block_id_type base;
	ds2i::progress_logger& m_plog;
	std::vector<uint8_t> m_buf;
};

/*
 * compute lambdas and compress in parallel for each posting list
 */
template<typename InputCollectionType>
struct lambdas_computer: ds2i::semiasync_queue::job {
	lambdas_computer(block_id_type block_id_base,
			typename InputCollectionType::document_enumerator e,
			ds2i::predictors_vec_type const& predictors,
			std::vector<uint32_t> const& counts, ds2i::progress_logger& plog,
			lambda_vector_type& lambda_points) :
			m_block_id_base(block_id_base), m_e(e), m_predictors(predictors), m_counts(
					counts), m_plog(plog), m_lambda_points(lambda_points) {

	}

	virtual void prepare() {
		using namespace ds2i;
		using namespace time_prediction;

		auto blocks = m_e.get_blocks();
		assert(m_counts.empty() || m_counts.size() == 2 * blocks.size());

		bool heuristic_greedy = configuration::get().heuristic_greedy;

		block_id_type cur_block_id = m_block_id_base;
		for (auto const& input_block : blocks) {
			static const uint32_t smoothing = 1;
			uint32_t docs_exp = smoothing, freqs_exp = smoothing;
			if (!m_counts.empty()) {
				docs_exp += m_counts[2 * input_block.index];
				freqs_exp += m_counts[2 * input_block.index + 1];
			}

			thread_local std::vector<uint32_t> values;

			auto append_lambdas =
					[&](std::vector<mixed_block::space_time_point>& points,
							block_id_type block_id) {
						// sort by lexicographical comparison of pair <space, time>
						std::sort(points.begin(), points.end());

						// smallest-space point is always added with lambda=0
						// thus m_points_buf will never be cleared
						m_points_buf.push_back(lambda_point {block_id, 0, points.front()});
						for (auto const& cur: points) {
							while (true) {
								auto const& prev = m_points_buf.back();
								// if this point is dominated we can skip it
								if (cur.time >= prev.st.time) break;
								// the smaller lambda is, the better the encoder is
								auto lambda = (cur.space - prev.st.space) / (prev.st.time - cur.time);
								// heuristic_greedy is true, then m_points_buf will never kick out lambdas,
								// on the other hand, when it is false (as default),points that are dominated
								// will be popped out
								// namely, each time a new point is calculated, it will kick out pointed that
								// are dominated by it
								if (!heuristic_greedy && lambda < prev.lambda) {
									m_points_buf.pop_back();
								} else {
									m_points_buf.push_back(lambda_point {block_id, lambda, cur});
									break;
								}
							}
						}
					};

			input_block.decode_doc_gaps(values);
			auto docs_sts = mixed_block::compute_space_time(values,
					input_block.doc_gaps_universe, m_predictors, docs_exp);
			append_lambdas(docs_sts, cur_block_id++);

			input_block.decode_freqs(values);
			auto freqs_sts = mixed_block::compute_space_time(values,
					uint32_t(-1), m_predictors, freqs_exp);
			append_lambdas(freqs_sts, cur_block_id++);
		}

	}

	virtual void commit() {
		std::copy(m_points_buf.begin(), m_points_buf.end(),
				std::back_inserter(m_lambda_points));
//		for (int i = 0; i < m_block_lambdas.size(); i++) {
//			std::cout << m_block_lambdas[i][0].block_id << std::endl;
//		}
//		for (block_lambdas_type::iterator it = m_block_lambdas.begin();
//				it != m_block_lambdas.end(); it++)
//			std::cout << it->first << std::endl;
		m_plog.done_sequence(m_e.size());
	}

	virtual ~lambdas_computer() {
	}

	block_id_type m_block_id_base;
	typename InputCollectionType::document_enumerator m_e;
	ds2i::predictors_vec_type const& m_predictors;
	std::vector<uint32_t> const& m_counts;
	ds2i::progress_logger& m_plog;
//	double m_lambda;
	std::vector<lambda_point> m_points_buf;
//	block_lambdas_type& m_block_lambdas;
	lambda_vector_type& m_lambda_points;
};

template<typename InputCollectionType>
void compute_lambdas(InputCollectionType const& input_coll,
		const char* predictors_filename, const char* block_stats_filename,
		const char* lambdas_filename,
		block_lambdas_type& block_doc_freq_lambdas) {
	using namespace ds2i;
	using namespace time_prediction;

	logger() << "Computing lambdas" << std::endl;
	progress_logger plog;

	auto predictors = load_predictors(predictors_filename);
	std::ifstream block_stats(block_stats_filename);

	double tick = get_time_usecs();
	double user_tick = get_user_time_usecs();

	uint32_t current_list_id;
	std::vector<block_id_type> block_counts;
	bool block_counts_consumed = true;
	block_id_type block_id_base = 0;
	size_t posting_zero_lists = 0;
	size_t posting_zero_blocks = 0;

	stxxl::syscall_file lpfile(lambdas_filename,
			stxxl::file::DIRECT | stxxl::file::CREAT | stxxl::file::RDWR);
	lambda_vector_type lambda_points(&lpfile);

	semiasync_queue queue(1 << 24);

//	block_lambdas_type block_doc_freq_lambdas;
	typedef lambdas_computer<InputCollectionType> job_type;

	for (size_t l = 0; l < input_coll.size(); ++l) {
		if (block_counts_consumed) {
			block_counts_consumed = false;
			read_block_stats(block_stats, current_list_id, block_counts);
		}

		auto e = input_coll[l];
		std::shared_ptr<job_type> job;

		// add jobs
		if (l == current_list_id) {
			posting_zero_blocks += std::accumulate(block_counts.begin(),
					block_counts.end(), size_t(0),
					[](size_t accum, uint32_t freq) {
						return accum + (freq == 0);
					});
			block_counts_consumed = true;
			job.reset(
					new job_type(block_id_base, e, predictors, block_counts,
							plog, lambda_points));
		} else {
			posting_zero_lists += 1;
			posting_zero_blocks += 2 * e.num_blocks();
			std::vector<uint32_t> empty_counts;
			job.reset(
					new job_type(block_id_base, e, predictors, empty_counts,
							plog, lambda_points));
		}
		block_id_base += 2 * e.num_blocks();
		queue.add_job(job, 2 * e.size());
	}
	stats_line()("freq_zero_lists", posting_zero_blocks)("freq_zero_blocks",
			posting_zero_lists);
	queue.complete();
	plog.log();

	for (lambda_vector_type::iterator it = lambda_points.begin();
			it != lambda_points.end(); it++) {
		block_doc_freq_lambdas[it->block_id].push_back(
				lambda_point { it->block_id, it->lambda, it->st });
	}

//	logger() << lambda_points.size() << " lambda points" << std::endl;
	double elapsed_secs = (get_time_usecs() - tick) / 1000000;
	double user_elapsed_secs = (get_user_time_usecs() - user_tick) / 1000000;

	stats_line()("worker_threads", configuration::get().worker_threads)(
			"lambda_computation_time", elapsed_secs)(
			"lambda_computation_user_time", user_elapsed_secs)("is_heuristic",
			configuration::get().heuristic_greedy);
}

template<typename InputCollectionType>
void bicriteria_hybrid_index(ds2i::global_parameters const& params,
		const char* predictors_filename, const char* block_stats_filename,
		const char* input_filename, const char* output_filename,
		const char* lambdas_filename, std::shared_ptr<bound> budget) {
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

	// global variables
	block_lambdas_type block_doc_freq_lambdas;
	solution_info sol_final;

	// FIRST, compute the lambdas for all the block

	if (boost::filesystem::exists(lambdas_filename)) {
		logger() << "Found lambdas file " << lambdas_filename
				<< ", skipping recomputation" << std::endl;
		logger() << "To recompute lambdas, remove file" << std::endl;

		stxxl::syscall_file lpfile(lambdas_filename,
				stxxl::file::DIRECT | stxxl::file::RDONLY);
		lambda_vector_type lambda_points(&lpfile);

		for (lambda_vector_type::iterator it = lambda_points.begin();
				it != lambda_points.end(); it++) {
			block_doc_freq_lambdas[it->block_id].push_back(
					lambda_point { it->block_id, it->lambda, it->st });
		}
	} else {
		compute_lambdas(input_coll, predictors_filename, block_stats_filename,
				lambdas_filename, block_doc_freq_lambdas);

	}
#ifndef NDEBUG
	logger() << "now we have calculated all the lambdas for " << num_blocks
			<< " blocks in current list." << std::endl;
#endif

	// SECOND, find the optimal encodings of each block

	double tick = get_time_usecs();
	double user_tick = get_user_time_usecs();

	double time_base = 0;
	logger() << "Computing space-time tradeoffs" << std::endl;
	/*****************************************************
	 * step 1: initialize two extreme paths
	 ****************************************************/
	auto basis = initializeSpaceTimeSolutions(block_doc_freq_lambdas, budget,
			space_base, time_base);

#ifndef NDEBUG
	print_basis(basis);
#endif

	if (basis.get_mu() < 0) {
		// early return found! we will skip following steps and compress immediately.
		std::tie(sol_final, sol_final) = basis.get_basis();
	} else {
		// next optimize the basis to squeeze the range between
		// UB and LB
		/*****************************************************
		 * step 2: recursively intersect pi_l and pi_r to approximate the boundary
		 ****************************************************/
		optimize(basis, block_doc_freq_lambdas, budget, space_base, time_base);

		//next swap UB and LB if needed
		/*****************************************************
		 * step 3: combine UB and LB into one path
		 ****************************************************/
		sol_final = swapPath(basis, block_doc_freq_lambdas, space_base,
				time_base);

	}

	double elapsed_secs = (get_time_usecs() - tick) / 1000000;
	double user_elapsed_secs = (get_user_time_usecs() - user_tick) / 1000000;

	stats_line()("worker_threads", configuration::get().worker_threads)(
			"greedy_time", elapsed_secs)("greedy_user_time", user_elapsed_secs);
	logger() << "Found trade-off. Space: " << sol_final.get_space() << " Time: "
			<< sol_final.get_time() << std::endl;
	stats_line()("found_space", sol_final.get_space())("found_time",
			sol_final.get_time());

	// THIRD, re-compress all the blocks OR collect statistics
	if (output_filename) {
		typedef typename block_mixed_index::builder builder_type;
		builder_type builder(input_coll.num_docs(), params);
		progress_logger plog;
		semiasync_queue queue(1 << 24);

		tick = get_time_usecs();
		user_tick = get_user_time_usecs();

		std::vector<int>::iterator it = sol_final.get_index().begin();

		block_id_type block_base = 0;
		for (size_t l = 0; l < input_coll.size(); ++l) {
			auto e = input_coll[l];

			typedef list_transformer<InputCollectionType, builder_type> job_type;
			std::shared_ptr<job_type> job(
					new job_type(builder, e, block_doc_freq_lambdas, block_base,
							it, plog));
			block_base += 2 * e.num_blocks();
			it += 2 * e.num_blocks();
			queue.add_job(job, 2 * e.size());
		}

		assert(block_base == num_blocks);
		assert(it == sol_final.get_index().end());
		queue.complete();
		plog.log();

		block_mixed_index coll;
		builder.build(coll);

		elapsed_secs = (get_time_usecs() - tick) / 1000000;
		user_elapsed_secs = (get_user_time_usecs() - user_tick) / 1000000;
		logger() << "Collection built in " << elapsed_secs << " seconds"
				<< std::endl;

		stats_line()("worker_threads", configuration::get().worker_threads)(
				"construction_time", elapsed_secs)("construction_user_time",
				user_elapsed_secs);
		dump_stats(coll, "block_mixed", plog.postings);

		succinct::mapper::freeze(coll, output_filename);

	} else {
		// collect statistics of blocks using different encoders
		std::map<type_param_pair, size_t> type_counts;
		auto it = sol_final.get_index().begin();
		for (block_id_type i = 0; i < sol_final.get_index().size(); i++, it++) {
			type_counts[type_param_pair(
					(uint8_t) block_doc_freq_lambdas[i][*it].st.type,
					block_doc_freq_lambdas[i][*it].st.param)] += 1;
		}
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

		stats_line()("blocks", num_blocks)("partial_blocks", partial_blocks)(
				"type_counts", type_counts_vec);
	}
}

int main(int argc, const char** argv) {

	using namespace ds2i;

	if (argc < 5) {
		std::cerr << "Usage: " << argv[0]
				<< " <index type> <predictors> <block_stats> <input_index> <lambdas_filename> <budget> [output_index] [--check <collection_basename>]"
				<< std::endl;
		return 1;
	}

	std::string type = argv[1];
	const char* predictors_filename = argv[2];
	const char* block_stats_filename = argv[3];
	const char* input_filename = argv[4];
	const char* lambdas_filename = argv[5];
//	size_t budget = boost::lexical_cast<size_t>(argv[6]);

	std::shared_ptr<bound> budget = add_bound(argv[6]);

	const char* output_filename = nullptr;
	if (argc > 7) {
		output_filename = argv[7];
	}

	bool check = false;
	const char* collection_basename = nullptr;
	if (argc > 9 && std::string(argv[8]) == "--check") {
		check = true;
		collection_basename = argv[9];
	}

	ds2i::global_parameters params;

	if (false) {
#define LOOP_BODY(R, DATA, T)                                           \
        } else if (type == BOOST_PP_STRINGIZE(T)) {                     \
            bicriteria_hybrid_index<BOOST_PP_CAT(T, _index)>               \
                (params, predictors_filename, block_stats_filename,     \
                 input_filename, output_filename,lambdas_filename,  budget); \
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
