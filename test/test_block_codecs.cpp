#define BOOST_TEST_MODULE block_codecs

#include "succinct/test_common.hpp"
#include "block_codecs.hpp"
#include "mixed_block.hpp"
#include <vector>
#include <cstdlib>

template<typename BlockCodec>
void test_block_codec() {
	std::vector<size_t> sizes = { /*1, 16, BlockCodec::block_size - 1,*/
	BlockCodec::block_size, 256, 384, 512, 640, 768, 896, 1024, 2048, 4096,
			8192, 16384, 32768, 65536 };
	for (auto size : sizes) {
		std::vector<uint32_t> values(size);
//		for (uint32_t i = 0; i < size / 128; i++) {
//			std::generate(values.begin() + 128 * i, values.end(),
//					[&]() {return (uint32_t)rand() % (1 << (4 + 2 * i));});
//		}
		std::generate(values.begin(), values.end(),
				[]() {return (uint32_t)rand() % (1 << 12);});

		for (size_t tcase = 0; tcase < 2; ++tcase) {
			// actually non of those three encoders need
			// @param sum_of_values.
			// test both undefined and given sum_of_values
			uint32_t sum_of_values(-1);
			if (tcase == 1) {
				sum_of_values = std::accumulate(values.begin(), values.end(),
						0);
			}
			std::vector<uint8_t> encoded;

			BlockCodec::encode(values.data(), sum_of_values, values.size(),
					encoded);
			if (size > 128 && tcase == 1) {
				std::cout << "uncompressed size: " << size << std::endl;
				std::cout << "compressed size: " << encoded.size() << std::endl;

				ds2i::time_prediction::feature_vector fv;
				ds2i::time_prediction::values_statistics(values, fv);
				std::cout << "entropy: "
						<< fv[ds2i::time_prediction::feature_type::entropy]
						<< std::endl;

				std::vector<uint8_t> temp;
				for (uint32_t i = 0; i < size / 128; i++) {

					std::vector<uint32_t> subset;
					for (uint32_t j = 0; j < 128; j++) {
						subset.push_back(values[j + 128 * i]);
					}
					ds2i::time_prediction::values_statistics(subset, fv);
					std::cout << i << " entropy:"
							<< fv[ds2i::time_prediction::feature_type::entropy]
							<< std::endl;

					temp.clear();
					BlockCodec::encode(values.data() + 128 * i, sum_of_values,
							128, temp);
					std::cout << i << ": " << temp.size() << std::endl;
				}
			}

			std::vector<uint32_t> decoded(values.size());

			uint8_t const* out = BlockCodec::decode(encoded.data(),
					decoded.data(), sum_of_values, values.size());

			BOOST_REQUIRE_EQUAL(encoded.size(), out - encoded.data());
			BOOST_REQUIRE_EQUAL_COLLECTIONS(values.begin(), values.end(),
					decoded.begin(), decoded.end());
		}
	}
}

template<>
void test_block_codec<ds2i::mixed_block>() {
	std::vector<size_t> sizes = { /*1, 16, BlockCodec::block_size - 1,*/
	ds2i::mixed_block::block_size, 256, 384, 512, 640, 768, 896, 1024, 2048,
			4096 };
	for (auto size : sizes) {
		std::vector<uint32_t> values(size);
		std::generate(values.begin(), values.end(),
				[]() {return (uint32_t)rand() % (1 << 12);});

		for (size_t tcase = 0; tcase < 2; ++tcase) {
			// test both undefined and given sum_of_values
			uint32_t sum_of_values(-1);
			if (tcase == 1) {
				sum_of_values = std::accumulate(values.begin(), values.end(),
						0);
			}
			std::vector<uint8_t> encoded;

			ds2i::mixed_block::encode_type((ds2i::mixed_block::block_type) 1, 0,
					values.data(), sum_of_values, values.size(), encoded);
//			if (size > 128) {
//				std::cout << "uncompressed size: " << size << std::endl;
//				std::cout << "compressed size: " << encoded.size() << std::endl;
//				std::vector<uint8_t> temp;
//				for (uint8_t i = 0; i < size / 128; i++) {
//					temp.clear();
//
//					ds2i::mixed_block::encode_type(
//							(ds2i::mixed_block::block_type) 1, 0,
//							values.data() + 128 * i, sum_of_values, 128, temp);
//					std::cout << i << "-th block compressed size: "
//							<< temp.size() << std::endl;
//				}
//			}

			std::vector<uint32_t> decoded(values.size());

			uint8_t const* out = ds2i::mixed_block::decode(encoded.data(),
					decoded.data(), sum_of_values, values.size());

			BOOST_REQUIRE_EQUAL(encoded.size(), out - encoded.data());
			BOOST_REQUIRE_EQUAL_COLLECTIONS(values.begin(), values.end(),
					decoded.begin(), decoded.end());
		}
	}
}

BOOST_AUTO_TEST_CASE(block_codecs) {
	test_block_codec<ds2i::optpfor_block>();
	test_block_codec<ds2i::varint_G8IU_block>();
	test_block_codec<ds2i::interpolative_block>();
	test_block_codec<ds2i::mixed_block>();
}
