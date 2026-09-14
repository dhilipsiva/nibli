#define SOUFFLE_GENERATOR_VERSION ""
#include "souffle/CompiledSouffle.h"
#include "souffle/SignalHandler.h"
#include "souffle/SouffleInterface.h"
#include "souffle/datastructure/BTree.h"
#include "souffle/io/IOSystem.h"
#include "souffle/utility/MiscUtil.h"
#include <any>
namespace functors {
extern "C" {
}
} //namespace functors
namespace souffle::t_btree_000_iiiii__0_1_2_3_4__11111 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 5;
using t_tuple = Tuple<RamDomain, 5>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :((ramBitCast<RamSigned>(a[2]) < ramBitCast<RamSigned>(b[2])) ? -1 : (ramBitCast<RamSigned>(a[2]) > ramBitCast<RamSigned>(b[2])) ? 1 :((ramBitCast<RamSigned>(a[3]) < ramBitCast<RamSigned>(b[3])) ? -1 : (ramBitCast<RamSigned>(a[3]) > ramBitCast<RamSigned>(b[3])) ? 1 :((ramBitCast<RamSigned>(a[4]) < ramBitCast<RamSigned>(b[4])) ? -1 : (ramBitCast<RamSigned>(a[4]) > ramBitCast<RamSigned>(b[4])) ? 1 :(0)))));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))|| ((ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1])) && ((ramBitCast<RamSigned>(a[2]) < ramBitCast<RamSigned>(b[2]))|| ((ramBitCast<RamSigned>(a[2]) == ramBitCast<RamSigned>(b[2])) && ((ramBitCast<RamSigned>(a[3]) < ramBitCast<RamSigned>(b[3]))|| ((ramBitCast<RamSigned>(a[3]) == ramBitCast<RamSigned>(b[3])) && ((ramBitCast<RamSigned>(a[4]) < ramBitCast<RamSigned>(b[4]))))))))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]))&&(ramBitCast<RamSigned>(a[2]) == ramBitCast<RamSigned>(b[2]))&&(ramBitCast<RamSigned>(a[3]) == ramBitCast<RamSigned>(b[3]))&&(ramBitCast<RamSigned>(a[4]) == ramBitCast<RamSigned>(b[4]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1,RamDomain a2,RamDomain a3,RamDomain a4);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_00000(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_00000(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_11111(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_11111(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_iiiii__0_1_2_3_4__11111 
namespace souffle::t_btree_000_iiiii__0_1_2_3_4__11111 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[5];
std::copy(ramDomain, ramDomain + 5, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1,RamDomain a2,RamDomain a3,RamDomain a4) {
RamDomain data[5] = {a0,a1,a2,a3,a4};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_00000(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_00000(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_11111(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_11111(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_11111(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 5 direct b-tree index 0 lex-order [0,1,2,3,4]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_iiiii__0_1_2_3_4__11111 
namespace souffle::t_btree_000_iii__0_1_2__111 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 3;
using t_tuple = Tuple<RamDomain, 3>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :((ramBitCast<RamSigned>(a[2]) < ramBitCast<RamSigned>(b[2])) ? -1 : (ramBitCast<RamSigned>(a[2]) > ramBitCast<RamSigned>(b[2])) ? 1 :(0)));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))|| ((ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1])) && ((ramBitCast<RamSigned>(a[2]) < ramBitCast<RamSigned>(b[2]))))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]))&&(ramBitCast<RamSigned>(a[2]) == ramBitCast<RamSigned>(b[2]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1,RamDomain a2);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_000(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_000(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_111(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_111(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_iii__0_1_2__111 
namespace souffle::t_btree_000_iii__0_1_2__111 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[3];
std::copy(ramDomain, ramDomain + 3, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1,RamDomain a2) {
RamDomain data[3] = {a0,a1,a2};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_000(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_000(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_111(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_111(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_111(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 3 direct b-tree index 0 lex-order [0,1,2]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_iii__0_1_2__111 
namespace souffle::t_btree_000_ii__0_1__11 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 2;
using t_tuple = Tuple<RamDomain, 2>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :(0));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_ii__0_1__11 
namespace souffle::t_btree_000_ii__0_1__11 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[2];
std::copy(ramDomain, ramDomain + 2, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1) {
RamDomain data[2] = {a0,a1};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_11(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 2 direct b-tree index 0 lex-order [0,1]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_ii__0_1__11 
namespace souffle::t_btree_000_i__0__1 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 1;
using t_tuple = Tuple<RamDomain, 1>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :(0);
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_i__0__1 
namespace souffle::t_btree_000_i__0__1 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[1];
std::copy(ramDomain, ramDomain + 1, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0) {
RamDomain data[1] = {a0};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_1(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 1 direct b-tree index 0 lex-order [0]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_i__0__1 
namespace  souffle {
using namespace souffle;
class Stratum_answer_6c655231fec607ba {
public:
 Stratum_answer_6c655231fec607ba(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_i__0__1::Type& rel_answer_227ae7ad3b0ead1f,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iii__0_1_2__111::Type& rel_p_warns_a31319bd838ae612);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_i__0__1::Type* rel_answer_227ae7ad3b0ead1f;
t_btree_000_iii__0_1_2__111::Type* rel_p_authorized_3b4f94c44af63fd0;
t_btree_000_iii__0_1_2__111::Type* rel_p_warns_a31319bd838ae612;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_answer_6c655231fec607ba::Stratum_answer_6c655231fec607ba(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_i__0__1::Type& rel_answer_227ae7ad3b0ead1f,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iii__0_1_2__111::Type& rel_p_warns_a31319bd838ae612):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_answer_227ae7ad3b0ead1f(&rel_answer_227ae7ad3b0ead1f),
rel_p_authorized_3b4f94c44af63fd0(&rel_p_authorized_3b4f94c44af63fd0),
rel_p_warns_a31319bd838ae612(&rel_p_warns_a31319bd838ae612){
}

void Stratum_answer_6c655231fec607ba::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
signalHandler->setMsg(R"_(answer(0) :- 
   p_warns("Gate","F0","S0").
in file input.dl [16:1-16:40])_");
if(!(rel_p_warns_a31319bd838ae612->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt,rel_answer_227ae7ad3b0ead1f->createContext());
CREATE_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt,rel_p_warns_a31319bd838ae612->createContext());
if(rel_p_warns_a31319bd838ae612->contains(Tuple<RamDomain,3>{{ramBitCast(RamSigned(0)),ramBitCast(RamSigned(1)),ramBitCast(RamSigned(2))}},READ_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt))) {
Tuple<RamDomain,1> tuple{{ramBitCast(RamSigned(0))}};
rel_answer_227ae7ad3b0ead1f->insert(tuple,READ_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt));
}
}
();}
signalHandler->setMsg(R"_(answer(1) :- 
   p_warns("Gate","F1","S1").
in file input.dl [17:1-17:40])_");
if(!(rel_p_warns_a31319bd838ae612->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt,rel_answer_227ae7ad3b0ead1f->createContext());
CREATE_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt,rel_p_warns_a31319bd838ae612->createContext());
if(rel_p_warns_a31319bd838ae612->contains(Tuple<RamDomain,3>{{ramBitCast(RamSigned(0)),ramBitCast(RamSigned(3)),ramBitCast(RamSigned(4))}},READ_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt))) {
Tuple<RamDomain,1> tuple{{ramBitCast(RamSigned(1))}};
rel_answer_227ae7ad3b0ead1f->insert(tuple,READ_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt));
}
}
();}
signalHandler->setMsg(R"_(answer(2) :- 
   p_authorized("F2","Release","S2").
in file input.dl [18:1-18:48])_");
if(!(rel_p_authorized_3b4f94c44af63fd0->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt,rel_answer_227ae7ad3b0ead1f->createContext());
CREATE_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt,rel_p_authorized_3b4f94c44af63fd0->createContext());
if(rel_p_authorized_3b4f94c44af63fd0->contains(Tuple<RamDomain,3>{{ramBitCast(RamSigned(5)),ramBitCast(RamSigned(6)),ramBitCast(RamSigned(7))}},READ_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt))) {
Tuple<RamDomain,1> tuple{{ramBitCast(RamSigned(2))}};
rel_answer_227ae7ad3b0ead1f->insert(tuple,READ_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt));
}
}
();}
signalHandler->setMsg(R"_(answer(3) :- 
   p_warns("Gate","F3","S3").
in file input.dl [19:1-19:40])_");
if(!(rel_p_warns_a31319bd838ae612->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt,rel_answer_227ae7ad3b0ead1f->createContext());
CREATE_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt,rel_p_warns_a31319bd838ae612->createContext());
if(rel_p_warns_a31319bd838ae612->contains(Tuple<RamDomain,3>{{ramBitCast(RamSigned(0)),ramBitCast(RamSigned(8)),ramBitCast(RamSigned(9))}},READ_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt))) {
Tuple<RamDomain,1> tuple{{ramBitCast(RamSigned(3))}};
rel_answer_227ae7ad3b0ead1f->insert(tuple,READ_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt));
}
}
();}
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(i)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(name)_",R"_(answer)_"},{R"_(operation)_",R"_(output)_"},{R"_(output-dir)_",R"_(.)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 1, "params": ["i"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 1, "types": ["i:number"]}})_"}});
if (outputDirectory == "-"){directiveMap["IO"] = "stdout"; directiveMap["headers"] = "true";}
else if (!outputDirectory.empty()) {directiveMap["output-dir"] = outputDirectory;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}
if (pruneImdtRels) rel_p_authorized_3b4f94c44af63fd0->purge();
if (pruneImdtRels) rel_p_warns_a31319bd838ae612->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_authorized_7aa9faa5dcc77546 {
public:
 Stratum_p_authorized_7aa9faa5dcc77546(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1,t_btree_000_iii__0_1_2__111::Type& rel_p_dangerous_d0dd5fbc04aa6c6a,t_btree_000_iii__0_1_2__111::Type& rel_p_permits_bff897f9d6b85db2,t_btree_000_ii__0_1__11::Type& rel_p_prevents_d66348ddd9bf0aaf);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_iii__0_1_2__111::Type* rel_p_authorized_3b4f94c44af63fd0;
t_btree_000_iiiii__0_1_2_3_4__11111::Type* rel_p_carries_18ed98dca8dc70c1;
t_btree_000_iii__0_1_2__111::Type* rel_p_dangerous_d0dd5fbc04aa6c6a;
t_btree_000_iii__0_1_2__111::Type* rel_p_permits_bff897f9d6b85db2;
t_btree_000_ii__0_1__11::Type* rel_p_prevents_d66348ddd9bf0aaf;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_authorized_7aa9faa5dcc77546::Stratum_p_authorized_7aa9faa5dcc77546(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1,t_btree_000_iii__0_1_2__111::Type& rel_p_dangerous_d0dd5fbc04aa6c6a,t_btree_000_iii__0_1_2__111::Type& rel_p_permits_bff897f9d6b85db2,t_btree_000_ii__0_1__11::Type& rel_p_prevents_d66348ddd9bf0aaf):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_authorized_3b4f94c44af63fd0(&rel_p_authorized_3b4f94c44af63fd0),
rel_p_carries_18ed98dca8dc70c1(&rel_p_carries_18ed98dca8dc70c1),
rel_p_dangerous_d0dd5fbc04aa6c6a(&rel_p_dangerous_d0dd5fbc04aa6c6a),
rel_p_permits_bff897f9d6b85db2(&rel_p_permits_bff897f9d6b85db2),
rel_p_prevents_d66348ddd9bf0aaf(&rel_p_prevents_d66348ddd9bf0aaf){
}

void Stratum_p_authorized_7aa9faa5dcc77546::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
signalHandler->setMsg(R"_(p_authorized(F,"Release",S) :- 
   p_carries(F,D,S,_,_),
   p_dangerous(S,D,"Exploit"),
   p_prevents("Sanitizer",F).
in file input.dl [11:1-11:108])_");
if(!(rel_p_dangerous_d0dd5fbc04aa6c6a->empty()) && !(rel_p_prevents_d66348ddd9bf0aaf->empty()) && !(rel_p_carries_18ed98dca8dc70c1->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt,rel_p_authorized_3b4f94c44af63fd0->createContext());
CREATE_OP_CONTEXT(rel_p_carries_18ed98dca8dc70c1_op_ctxt,rel_p_carries_18ed98dca8dc70c1->createContext());
CREATE_OP_CONTEXT(rel_p_dangerous_d0dd5fbc04aa6c6a_op_ctxt,rel_p_dangerous_d0dd5fbc04aa6c6a->createContext());
CREATE_OP_CONTEXT(rel_p_prevents_d66348ddd9bf0aaf_op_ctxt,rel_p_prevents_d66348ddd9bf0aaf->createContext());
for(const auto& env0 : *rel_p_carries_18ed98dca8dc70c1) {
if( rel_p_prevents_d66348ddd9bf0aaf->contains(Tuple<RamDomain,2>{{ramBitCast(RamSigned(10)),ramBitCast(env0[0])}},READ_OP_CONTEXT(rel_p_prevents_d66348ddd9bf0aaf_op_ctxt)) && rel_p_dangerous_d0dd5fbc04aa6c6a->contains(Tuple<RamDomain,3>{{ramBitCast(env0[2]),ramBitCast(env0[1]),ramBitCast(RamSigned(11))}},READ_OP_CONTEXT(rel_p_dangerous_d0dd5fbc04aa6c6a_op_ctxt))) {
Tuple<RamDomain,3> tuple{{ramBitCast(env0[0]),ramBitCast(RamSigned(6)),ramBitCast(env0[2])}};
rel_p_authorized_3b4f94c44af63fd0->insert(tuple,READ_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt));
}
}
}
();}
signalHandler->setMsg(R"_(p_authorized(F,"Release",S) :- 
   p_carries(F,D,S,_,_),
   p_dangerous(S,D,"Exploit"),
   p_permits("Review",F,"Waiver").
in file input.dl [12:1-12:113])_");
if(!(rel_p_dangerous_d0dd5fbc04aa6c6a->empty()) && !(rel_p_permits_bff897f9d6b85db2->empty()) && !(rel_p_carries_18ed98dca8dc70c1->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt,rel_p_authorized_3b4f94c44af63fd0->createContext());
CREATE_OP_CONTEXT(rel_p_carries_18ed98dca8dc70c1_op_ctxt,rel_p_carries_18ed98dca8dc70c1->createContext());
CREATE_OP_CONTEXT(rel_p_dangerous_d0dd5fbc04aa6c6a_op_ctxt,rel_p_dangerous_d0dd5fbc04aa6c6a->createContext());
CREATE_OP_CONTEXT(rel_p_permits_bff897f9d6b85db2_op_ctxt,rel_p_permits_bff897f9d6b85db2->createContext());
for(const auto& env0 : *rel_p_carries_18ed98dca8dc70c1) {
if( rel_p_permits_bff897f9d6b85db2->contains(Tuple<RamDomain,3>{{ramBitCast(RamSigned(12)),ramBitCast(env0[0]),ramBitCast(RamSigned(13))}},READ_OP_CONTEXT(rel_p_permits_bff897f9d6b85db2_op_ctxt)) && rel_p_dangerous_d0dd5fbc04aa6c6a->contains(Tuple<RamDomain,3>{{ramBitCast(env0[2]),ramBitCast(env0[1]),ramBitCast(RamSigned(11))}},READ_OP_CONTEXT(rel_p_dangerous_d0dd5fbc04aa6c6a_op_ctxt))) {
Tuple<RamDomain,3> tuple{{ramBitCast(env0[0]),ramBitCast(RamSigned(6)),ramBitCast(env0[2])}};
rel_p_authorized_3b4f94c44af63fd0->insert(tuple,READ_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt));
}
}
}
();}
if (pruneImdtRels) rel_p_dangerous_d0dd5fbc04aa6c6a->purge();
if (pruneImdtRels) rel_p_permits_bff897f9d6b85db2->purge();
if (pruneImdtRels) rel_p_prevents_d66348ddd9bf0aaf->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_carries_13889210c0533e9a {
public:
 Stratum_p_carries_13889210c0533e9a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_iiiii__0_1_2_3_4__11111::Type* rel_p_carries_18ed98dca8dc70c1;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_carries_13889210c0533e9a::Stratum_p_carries_13889210c0533e9a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_carries_18ed98dca8dc70c1(&rel_p_carries_18ed98dca8dc70c1){
}

void Stratum_p_carries_13889210c0533e9a::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2	a3	a4)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_carries)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 5, "params": ["a0", "a1", "a2", "a3", "a4"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 5, "types": ["s:symbol", "s:symbol", "s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_carries_18ed98dca8dc70c1);
} catch (std::exception& e) {std::cerr << "Error loading p_carries data: " << e.what() << '\n';
exit(1);
}
}
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_dangerous_e168760b98a227ac {
public:
 Stratum_p_dangerous_e168760b98a227ac(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_dangerous_d0dd5fbc04aa6c6a);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_iii__0_1_2__111::Type* rel_p_dangerous_d0dd5fbc04aa6c6a;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_dangerous_e168760b98a227ac::Stratum_p_dangerous_e168760b98a227ac(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_dangerous_d0dd5fbc04aa6c6a):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_dangerous_d0dd5fbc04aa6c6a(&rel_p_dangerous_d0dd5fbc04aa6c6a){
}

void Stratum_p_dangerous_e168760b98a227ac::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_dangerous)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 3, "params": ["a0", "a1", "a2"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 3, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_dangerous_d0dd5fbc04aa6c6a);
} catch (std::exception& e) {std::cerr << "Error loading p_dangerous data: " << e.what() << '\n';
exit(1);
}
}
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_permits_867f1bb45ca6e00a {
public:
 Stratum_p_permits_867f1bb45ca6e00a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_permits_bff897f9d6b85db2);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_iii__0_1_2__111::Type* rel_p_permits_bff897f9d6b85db2;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_permits_867f1bb45ca6e00a::Stratum_p_permits_867f1bb45ca6e00a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_permits_bff897f9d6b85db2):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_permits_bff897f9d6b85db2(&rel_p_permits_bff897f9d6b85db2){
}

void Stratum_p_permits_867f1bb45ca6e00a::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_permits)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 3, "params": ["a0", "a1", "a2"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 3, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_permits_bff897f9d6b85db2);
} catch (std::exception& e) {std::cerr << "Error loading p_permits data: " << e.what() << '\n';
exit(1);
}
}
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_prevents_33daed023f64e10a {
public:
 Stratum_p_prevents_33daed023f64e10a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11::Type& rel_p_prevents_d66348ddd9bf0aaf);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_ii__0_1__11::Type* rel_p_prevents_d66348ddd9bf0aaf;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_prevents_33daed023f64e10a::Stratum_p_prevents_33daed023f64e10a(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11::Type& rel_p_prevents_d66348ddd9bf0aaf):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_prevents_d66348ddd9bf0aaf(&rel_p_prevents_d66348ddd9bf0aaf){
}

void Stratum_p_prevents_33daed023f64e10a::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_prevents)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 2, "params": ["a0", "a1"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 2, "types": ["s:symbol", "s:symbol"]}})_"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_prevents_d66348ddd9bf0aaf);
} catch (std::exception& e) {std::cerr << "Error loading p_prevents data: " << e.what() << '\n';
exit(1);
}
}
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_warns_002038b1e8a2d323 {
public:
 Stratum_p_warns_002038b1e8a2d323(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1,t_btree_000_iii__0_1_2__111::Type& rel_p_warns_a31319bd838ae612);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_iii__0_1_2__111::Type* rel_p_authorized_3b4f94c44af63fd0;
t_btree_000_iiiii__0_1_2_3_4__11111::Type* rel_p_carries_18ed98dca8dc70c1;
t_btree_000_iii__0_1_2__111::Type* rel_p_warns_a31319bd838ae612;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_warns_002038b1e8a2d323::Stratum_p_warns_002038b1e8a2d323(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_iii__0_1_2__111::Type& rel_p_authorized_3b4f94c44af63fd0,t_btree_000_iiiii__0_1_2_3_4__11111::Type& rel_p_carries_18ed98dca8dc70c1,t_btree_000_iii__0_1_2__111::Type& rel_p_warns_a31319bd838ae612):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_p_authorized_3b4f94c44af63fd0(&rel_p_authorized_3b4f94c44af63fd0),
rel_p_carries_18ed98dca8dc70c1(&rel_p_carries_18ed98dca8dc70c1),
rel_p_warns_a31319bd838ae612(&rel_p_warns_a31319bd838ae612){
}

void Stratum_p_warns_002038b1e8a2d323::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
signalHandler->setMsg(R"_(p_warns("Gate",F,S) :- 
   p_carries(F,_,S,_,_),
   !p_authorized(F,"Release",S).
in file input.dl [13:1-13:75])_");
if(!(rel_p_carries_18ed98dca8dc70c1->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt,rel_p_authorized_3b4f94c44af63fd0->createContext());
CREATE_OP_CONTEXT(rel_p_carries_18ed98dca8dc70c1_op_ctxt,rel_p_carries_18ed98dca8dc70c1->createContext());
CREATE_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt,rel_p_warns_a31319bd838ae612->createContext());
for(const auto& env0 : *rel_p_carries_18ed98dca8dc70c1) {
if( !(rel_p_authorized_3b4f94c44af63fd0->contains(Tuple<RamDomain,3>{{ramBitCast(env0[0]),ramBitCast(RamSigned(6)),ramBitCast(env0[2])}},READ_OP_CONTEXT(rel_p_authorized_3b4f94c44af63fd0_op_ctxt)))) {
Tuple<RamDomain,3> tuple{{ramBitCast(RamSigned(0)),ramBitCast(env0[0]),ramBitCast(env0[2])}};
rel_p_warns_a31319bd838ae612->insert(tuple,READ_OP_CONTEXT(rel_p_warns_a31319bd838ae612_op_ctxt));
}
}
}
();}
if (pruneImdtRels) rel_p_carries_18ed98dca8dc70c1->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Sf_program: public SouffleProgram {
public:
 Sf_program();
 ~Sf_program();
void run();
void runAll(std::string inputDirectoryArg = "",std::string outputDirectoryArg = "",bool performIOArg = true,bool pruneImdtRelsArg = true);
void printAll([[maybe_unused]] std::string outputDirectoryArg = "");
void loadAll([[maybe_unused]] std::string inputDirectoryArg = "");
void dumpInputs();
void dumpOutputs();
SymbolTable& getSymbolTable();
RecordTable& getRecordTable();
void setNumThreads(std::size_t numThreadsValue);
void executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret);
private:
void runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg);
SymbolTableImpl symTable;
SpecializedRecordTable<0> recordTable;
ConcurrentCache<std::string,std::regex> regexCache;
Own<t_btree_000_iiiii__0_1_2_3_4__11111::Type> rel_p_carries_18ed98dca8dc70c1;
souffle::RelationWrapper<t_btree_000_iiiii__0_1_2_3_4__11111::Type> wrapper_rel_p_carries_18ed98dca8dc70c1;
Own<t_btree_000_iii__0_1_2__111::Type> rel_p_dangerous_d0dd5fbc04aa6c6a;
souffle::RelationWrapper<t_btree_000_iii__0_1_2__111::Type> wrapper_rel_p_dangerous_d0dd5fbc04aa6c6a;
Own<t_btree_000_iii__0_1_2__111::Type> rel_p_permits_bff897f9d6b85db2;
souffle::RelationWrapper<t_btree_000_iii__0_1_2__111::Type> wrapper_rel_p_permits_bff897f9d6b85db2;
Own<t_btree_000_ii__0_1__11::Type> rel_p_prevents_d66348ddd9bf0aaf;
souffle::RelationWrapper<t_btree_000_ii__0_1__11::Type> wrapper_rel_p_prevents_d66348ddd9bf0aaf;
Own<t_btree_000_iii__0_1_2__111::Type> rel_p_authorized_3b4f94c44af63fd0;
souffle::RelationWrapper<t_btree_000_iii__0_1_2__111::Type> wrapper_rel_p_authorized_3b4f94c44af63fd0;
Own<t_btree_000_iii__0_1_2__111::Type> rel_p_warns_a31319bd838ae612;
souffle::RelationWrapper<t_btree_000_iii__0_1_2__111::Type> wrapper_rel_p_warns_a31319bd838ae612;
Own<t_btree_000_i__0__1::Type> rel_answer_227ae7ad3b0ead1f;
souffle::RelationWrapper<t_btree_000_i__0__1::Type> wrapper_rel_answer_227ae7ad3b0ead1f;
Stratum_answer_6c655231fec607ba stratum_answer_2f35c27c80acc152;
Stratum_p_authorized_7aa9faa5dcc77546 stratum_p_authorized_84627d4fd5e56373;
Stratum_p_carries_13889210c0533e9a stratum_p_carries_7745a77d5dd81fee;
Stratum_p_dangerous_e168760b98a227ac stratum_p_dangerous_b0a6cf0894e3d360;
Stratum_p_permits_867f1bb45ca6e00a stratum_p_permits_b625696c58df32f0;
Stratum_p_prevents_33daed023f64e10a stratum_p_prevents_c638bdec35d873c3;
Stratum_p_warns_002038b1e8a2d323 stratum_p_warns_630e2f0661b9b617;
std::string inputDirectory;
std::string outputDirectory;
SignalHandler* signalHandler{SignalHandler::instance()};
std::atomic<RamDomain> ctr{};
std::atomic<std::size_t> iter{};
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Sf_program::Sf_program():
symTable({
  R"_(Gate)_",
  R"_(F0)_",
  R"_(S0)_",
  R"_(F1)_",
  R"_(S1)_",
  R"_(F2)_",
  R"_(Release)_",
  R"_(S2)_",
  R"_(F3)_",
  R"_(S3)_",
  R"_(Sanitizer)_",
  R"_(Exploit)_",
  R"_(Review)_",
  R"_(Waiver)_",
}),
recordTable(),
regexCache(),
rel_p_carries_18ed98dca8dc70c1(mk<t_btree_000_iiiii__0_1_2_3_4__11111::Type>()),
wrapper_rel_p_carries_18ed98dca8dc70c1(0, *rel_p_carries_18ed98dca8dc70c1, *this, "p_carries", std::array<const char *,5>{{"s:symbol","s:symbol","s:symbol","s:symbol","s:symbol"}}, std::array<const char *,5>{{"a0","a1","a2","a3","a4"}}, 0),
rel_p_dangerous_d0dd5fbc04aa6c6a(mk<t_btree_000_iii__0_1_2__111::Type>()),
wrapper_rel_p_dangerous_d0dd5fbc04aa6c6a(1, *rel_p_dangerous_d0dd5fbc04aa6c6a, *this, "p_dangerous", std::array<const char *,3>{{"s:symbol","s:symbol","s:symbol"}}, std::array<const char *,3>{{"a0","a1","a2"}}, 0),
rel_p_permits_bff897f9d6b85db2(mk<t_btree_000_iii__0_1_2__111::Type>()),
wrapper_rel_p_permits_bff897f9d6b85db2(2, *rel_p_permits_bff897f9d6b85db2, *this, "p_permits", std::array<const char *,3>{{"s:symbol","s:symbol","s:symbol"}}, std::array<const char *,3>{{"a0","a1","a2"}}, 0),
rel_p_prevents_d66348ddd9bf0aaf(mk<t_btree_000_ii__0_1__11::Type>()),
wrapper_rel_p_prevents_d66348ddd9bf0aaf(3, *rel_p_prevents_d66348ddd9bf0aaf, *this, "p_prevents", std::array<const char *,2>{{"s:symbol","s:symbol"}}, std::array<const char *,2>{{"a0","a1"}}, 0),
rel_p_authorized_3b4f94c44af63fd0(mk<t_btree_000_iii__0_1_2__111::Type>()),
wrapper_rel_p_authorized_3b4f94c44af63fd0(4, *rel_p_authorized_3b4f94c44af63fd0, *this, "p_authorized", std::array<const char *,3>{{"s:symbol","s:symbol","s:symbol"}}, std::array<const char *,3>{{"a0","a1","a2"}}, 0),
rel_p_warns_a31319bd838ae612(mk<t_btree_000_iii__0_1_2__111::Type>()),
wrapper_rel_p_warns_a31319bd838ae612(5, *rel_p_warns_a31319bd838ae612, *this, "p_warns", std::array<const char *,3>{{"s:symbol","s:symbol","s:symbol"}}, std::array<const char *,3>{{"a0","a1","a2"}}, 0),
rel_answer_227ae7ad3b0ead1f(mk<t_btree_000_i__0__1::Type>()),
wrapper_rel_answer_227ae7ad3b0ead1f(6, *rel_answer_227ae7ad3b0ead1f, *this, "answer", std::array<const char *,1>{{"i:number"}}, std::array<const char *,1>{{"i"}}, 0),
stratum_answer_2f35c27c80acc152(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_answer_227ae7ad3b0ead1f,*rel_p_authorized_3b4f94c44af63fd0,*rel_p_warns_a31319bd838ae612),
stratum_p_authorized_84627d4fd5e56373(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_authorized_3b4f94c44af63fd0,*rel_p_carries_18ed98dca8dc70c1,*rel_p_dangerous_d0dd5fbc04aa6c6a,*rel_p_permits_bff897f9d6b85db2,*rel_p_prevents_d66348ddd9bf0aaf),
stratum_p_carries_7745a77d5dd81fee(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_carries_18ed98dca8dc70c1),
stratum_p_dangerous_b0a6cf0894e3d360(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_dangerous_d0dd5fbc04aa6c6a),
stratum_p_permits_b625696c58df32f0(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_permits_bff897f9d6b85db2),
stratum_p_prevents_c638bdec35d873c3(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_prevents_d66348ddd9bf0aaf),
stratum_p_warns_630e2f0661b9b617(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_p_authorized_3b4f94c44af63fd0,*rel_p_carries_18ed98dca8dc70c1,*rel_p_warns_a31319bd838ae612){
addRelation("p_carries", wrapper_rel_p_carries_18ed98dca8dc70c1, true, false);
addRelation("p_dangerous", wrapper_rel_p_dangerous_d0dd5fbc04aa6c6a, true, false);
addRelation("p_permits", wrapper_rel_p_permits_bff897f9d6b85db2, true, false);
addRelation("p_prevents", wrapper_rel_p_prevents_d66348ddd9bf0aaf, true, false);
addRelation("p_authorized", wrapper_rel_p_authorized_3b4f94c44af63fd0, false, false);
addRelation("p_warns", wrapper_rel_p_warns_a31319bd838ae612, false, false);
addRelation("answer", wrapper_rel_answer_227ae7ad3b0ead1f, false, true);
}

 Sf_program::~Sf_program(){
}

void Sf_program::runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){

    this->inputDirectory  = std::move(inputDirectoryArg);
    this->outputDirectory = std::move(outputDirectoryArg);
    this->performIO       = performIOArg;
    this->pruneImdtRels   = pruneImdtRelsArg;

    // set default threads (in embedded mode)
    // if this is not set, and omp is used, the default omp setting of number of cores is used.
#if defined(_OPENMP)
    if (0 < getNumThreads()) { omp_set_num_threads(static_cast<int>(getNumThreads())); }
#endif

    signalHandler->set();
// -- query evaluation --
{
 std::vector<RamDomain> args, ret;
stratum_p_carries_7745a77d5dd81fee.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_p_dangerous_b0a6cf0894e3d360.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_p_permits_b625696c58df32f0.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_p_prevents_c638bdec35d873c3.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_p_authorized_84627d4fd5e56373.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_p_warns_630e2f0661b9b617.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_answer_2f35c27c80acc152.run(args, ret);
}

// -- relation hint statistics --
signalHandler->reset();
}

void Sf_program::run(){
runFunction("", "", false, false);
}

void Sf_program::runAll(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){
runFunction(inputDirectoryArg, outputDirectoryArg, performIOArg, pruneImdtRelsArg);
}

void Sf_program::printAll([[maybe_unused]] std::string outputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(i)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(name)_",R"_(answer)_"},{R"_(operation)_",R"_(output)_"},{R"_(output-dir)_",R"_(.)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 1, "params": ["i"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 1, "types": ["i:number"]}})_"}});
if (!outputDirectoryArg.empty()) {directiveMap["output-dir"] = outputDirectoryArg;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_program::loadAll([[maybe_unused]] std::string inputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2	a3	a4)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_carries)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 5, "params": ["a0", "a1", "a2", "a3", "a4"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 5, "types": ["s:symbol", "s:symbol", "s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_carries_18ed98dca8dc70c1);
} catch (std::exception& e) {std::cerr << "Error loading p_carries data: " << e.what() << '\n';
exit(1);
}
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_dangerous)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 3, "params": ["a0", "a1", "a2"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 3, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_dangerous_d0dd5fbc04aa6c6a);
} catch (std::exception& e) {std::cerr << "Error loading p_dangerous data: " << e.what() << '\n';
exit(1);
}
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1	a2)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_permits)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 3, "params": ["a0", "a1", "a2"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 3, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_permits_bff897f9d6b85db2);
} catch (std::exception& e) {std::cerr << "Error loading p_permits data: " << e.what() << '\n';
exit(1);
}
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_prevents)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 2, "params": ["a0", "a1"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 2, "types": ["s:symbol", "s:symbol"]}})_"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_prevents_d66348ddd9bf0aaf);
} catch (std::exception& e) {std::cerr << "Error loading p_prevents data: " << e.what() << '\n';
exit(1);
}
}

void Sf_program::dumpInputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "p_carries";
rwOperation["types"] = R"_({"relation": {"arity": 5, "auxArity": 0, "types": ["s:symbol", "s:symbol", "s:symbol", "s:symbol", "s:symbol"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_p_carries_18ed98dca8dc70c1);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "p_dangerous";
rwOperation["types"] = R"_({"relation": {"arity": 3, "auxArity": 0, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_p_dangerous_d0dd5fbc04aa6c6a);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "p_permits";
rwOperation["types"] = R"_({"relation": {"arity": 3, "auxArity": 0, "types": ["s:symbol", "s:symbol", "s:symbol"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_p_permits_bff897f9d6b85db2);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "p_prevents";
rwOperation["types"] = R"_({"relation": {"arity": 2, "auxArity": 0, "types": ["s:symbol", "s:symbol"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_p_prevents_d66348ddd9bf0aaf);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_program::dumpOutputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "answer";
rwOperation["types"] = R"_({"relation": {"arity": 1, "auxArity": 0, "types": ["i:number"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

SymbolTable& Sf_program::getSymbolTable(){
return symTable;
}

RecordTable& Sf_program::getRecordTable(){
return recordTable;
}

void Sf_program::setNumThreads(std::size_t numThreadsValue){
SouffleProgram::setNumThreads(numThreadsValue);
symTable.setNumLanes(getNumThreads());
recordTable.setNumLanes(getNumThreads());
regexCache.setNumLanes(getNumThreads());
}

void Sf_program::executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret){
if (name == "answer") {
stratum_answer_2f35c27c80acc152.run(args, ret);
return;}
if (name == "p_authorized") {
stratum_p_authorized_84627d4fd5e56373.run(args, ret);
return;}
if (name == "p_carries") {
stratum_p_carries_7745a77d5dd81fee.run(args, ret);
return;}
if (name == "p_dangerous") {
stratum_p_dangerous_b0a6cf0894e3d360.run(args, ret);
return;}
if (name == "p_permits") {
stratum_p_permits_b625696c58df32f0.run(args, ret);
return;}
if (name == "p_prevents") {
stratum_p_prevents_c638bdec35d873c3.run(args, ret);
return;}
if (name == "p_warns") {
stratum_p_warns_630e2f0661b9b617.run(args, ret);
return;}
fatal(("unknown subroutine " + name).c_str());
}

} // namespace  souffle
namespace souffle {
SouffleProgram *newInstance_program(){return new  souffle::Sf_program;}
SymbolTable *getST_program(SouffleProgram *p){return &reinterpret_cast<souffle::Sf_program*>(p)->getSymbolTable();}
} // namespace souffle

#ifndef __EMBEDDED_SOUFFLE__
#include "souffle/CompiledOptions.h"
int main(int argc, char** argv)
{
try{
souffle::CmdOptions opt(R"_(/home/dhilipsiva/projects/dhilipsiva/nibli/paper/results/pilot/inputs/4/input.dl)_",
R"_()_",
R"_()_",
false,
R"_()_",
1);
if (!opt.parse(argc,argv)) return 1;
souffle::Sf_program obj;
#if defined(_OPENMP) 
obj.setNumThreads(opt.getNumJobs());

#endif
obj.runAll(opt.getInputFileDir(), opt.getOutputFileDir());
return 0;
} catch(std::exception &e) { souffle::SignalHandler::instance()->error(e.what());}
}
#endif

namespace  souffle {
using namespace souffle;
class factory_Sf_program: souffle::ProgramFactory {
public:
souffle::SouffleProgram* newInstance();
 factory_Sf_program();
private:
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
souffle::SouffleProgram* factory_Sf_program::newInstance(){
return new  souffle::Sf_program();
}

 factory_Sf_program::factory_Sf_program():
souffle::ProgramFactory("program"){
}

} // namespace  souffle
namespace souffle {

#ifdef __EMBEDDED_SOUFFLE__
extern "C" {
souffle::factory_Sf_program __factory_Sf_program_instance;
}
#endif
} // namespace souffle

