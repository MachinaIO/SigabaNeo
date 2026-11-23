// Enumerate the projective action on E7's 63 contact lines. The Python oracle
// uses this index to propose clauses; the Lean checks use only their witnesses.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <numeric>
#include <unordered_map>
#include <vector>

namespace {
using Mask = std::uint64_t;
constexpr int lines = 63;
constexpr int projective_order = 1451520;
using Perm = std::array<std::uint8_t, lines>;

struct WordStep { int parent, generator; };
struct Image { Mask mask; int element; };
struct Orbit { int seed; std::vector<Image> images; std::vector<int> offsets; };

std::vector<WordStep> words;
std::vector<Perm> elements;
std::vector<Mask> byte_actions, buffer;
std::vector<Orbit> orbits;

Mask key(const Perm &p, const int *axes) {
    Mask result = 0;
    for (int a = 0; a < 7; ++a)
        result = (result << 6) | p[axes[a]];
    return result;
}

// Pull a mask back by a generator, one input byte at a time.
Mask pull(Mask mask, int generator) {
    const Mask *table = &byte_actions[generator * 2048];
    Mask result = 0;
    for (int b = 0; b < 8; ++b) {
        result |= table[b * 256 + (mask & 255)];
        mask >>= 8;
    }
    return result;
}

void fill_orbit(Mask mask, int count) {
    buffer[0] = mask;
    for (int i = 1; i < count; ++i)
        buffer[i] = pull(buffer[words[i].parent], words[i].generator);
}
}

extern "C" int makegroup(int count, const std::uint8_t *generators, const int *axes) {
    std::unordered_map<Mask, int> seen;
    elements.reserve(projective_order);
    words.reserve(projective_order);
    seen.reserve(projective_order);
    byte_actions.resize(count * 2048);
    for (int g = 0; g < count; ++g) {
        const auto *p = generators + g * lines;
        for (int b = 0; b < 8; ++b) {
            for (int bits = 0; bits < 256; ++bits) {
                Mask result = 0;
                for (int i = 0; i < lines; ++i)
                    if (p[i] / 8 == b && ((bits >> (p[i] % 8)) & 1))
                        result |= Mask(1) << i;
                byte_actions[(g * 8 + b) * 256 + bits] = result;
            }
        }
    }
    Perm identity;
    std::iota(identity.begin(), identity.end(), 0);
    elements.push_back(identity);
    words.push_back({-1, -1});
    seen[key(identity, axes)] = 0;
    for (std::size_t i = 0; i < elements.size(); ++i) {
        for (int g = 0; g < count; ++g) {
            Perm product;
            for (int a = 0; a < lines; ++a)
                product[a] = elements[i][generators[g * lines + a]];
            auto [where, fresh] = seen.emplace(key(product, axes), elements.size());
            if (fresh) {
                elements.push_back(product);
                words.push_back({int(i), g});
            } else {
                assert(elements[where->second] == product);
            }
        }
    }
    buffer.resize(elements.size());
    return int(elements.size());
}

extern "C" int getword(int id, int *out, int capacity) {
    int length = 0;
    for (; id; id = words[id].parent) {
        if (length == capacity) return -1;
        out[length++] = words[id].generator;
    }
    std::reverse(out, out + length);
    return length;
}

extern "C" void permutation(int id, int *out) {
    std::copy(elements[id].begin(), elements[id].end(), out);
}

extern "C" int maximize(Mask mask) {
    for (int count : {1024, 32768, int(elements.size())}) {
        fill_orbit(mask, count);
        auto best = std::max_element(buffer.begin(), buffer.begin() + count);
        if (*best > mask) return int(best - buffer.begin());
    }
    return 0;
}

extern "C" int addbank(int seed, Mask mask) {
    fill_orbit(mask, int(elements.size()));
    Orbit orbit{seed, {}, {}};
    auto &images = orbit.images;
    images.resize(elements.size());
    for (int i = 0; i < int(images.size()); ++i)
        images[i] = {buffer[i], i};
    std::sort(images.begin(), images.end(), [](Image a, Image b) { return a.mask < b.mask; });
    images.erase(std::unique(images.begin(), images.end(),
                            [](Image a, Image b) { return a.mask == b.mask; }), images.end());
    images.shrink_to_fit();
    orbit.offsets.resize(32769);
    for (Image image : images) ++orbit.offsets[1 + (image.mask >> 48)];
    std::partial_sum(orbit.offsets.begin(), orbit.offsets.end(), orbit.offsets.begin());
    int count = int(images.size());
    orbits.push_back(std::move(orbit));
    return count;
}

// Enumerate submasks of the top 15 bits before testing the remaining bits.
extern "C" Mask contained(Mask mask, int *seed, int *element) {
    int high = int(mask >> 48);
    for (const auto &orbit : orbits) {
        for (int prefix = high; ; prefix = (prefix - 1) & high) {
            for (int i = orbit.offsets[prefix]; i < orbit.offsets[prefix + 1]; ++i) {
                Image hit = orbit.images[i];
                if ((hit.mask & ~mask) == 0) {
                    *seed = orbit.seed;
                    *element = hit.element;
                    return hit.mask;
                }
            }
            if (!prefix) break;
        }
    }
    return 0;
}
