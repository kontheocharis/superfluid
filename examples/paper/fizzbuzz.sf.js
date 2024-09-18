// boot.js

const { Buffer } = require("buffer");

// Type system
const Type = null;

// Equality
const Equal = (A) => (x) => (y) => null;

// Primitive types
const JsUnion = (A) => (B) => null;
const JsNull = null;
const JsUndefined = null;
const JsBool = null;
const JsArray = (T) => null;
const JsBigInt = null;
const JsUint = null;
const JsBoundedUint = (n) => null;
const JsNumber = null;
const JsString = null;

// Primitive values
const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;

// Conditional
const js_if = (A) => (cond) => (thenBranch) => (elseBranch) =>
  cond ? thenBranch() : elseBranch();
const js_if_dep = (A) => (b) => (thenBranch) => (elseBranch) =>
  b ? thenBranch() : elseBranch();

// Array operations
const js_empty_array = (T) => () => [];
const js_array_extend_l = (T) => (x) => (arr) => [x, ...arr];
const js_array_extend_r = (T) => (arr) => (x) => [...arr, x];
const js_array_switch_l =
  (T) => (E) => (emptyCase) => (nonEmptyCase) => (arr) =>
    arr.length === 0 ? emptyCase() : nonEmptyCase(arr[0])(arr.slice(1));
const js_array_switch_r =
  (T) => (E) => (emptyCase) => (nonEmptyCase) => (arr) =>
    arr.length === 0
      ? emptyCase()
      : nonEmptyCase(arr.slice(0, -1))(arr[arr.length - 1]);
const js_slice = (T) => (arr) => (start) => (end) => arr.slice(start, end);
const js_length = (T) => (arr) => arr.length;
const js_map = (A) => (B) => (a) => (fn) => a.map((x, i) => fn([x, i]));
const js_reduce = (T) => (C) => (fn) => (initial) => (arr) =>
  arr.reduce((acc, val) => fn(acc)(val), initial);
const js_index = (T) => (a) => (n) => a[n];

// Number operations
const js_zero = 0;
const js_one = 1;
const js_uint_zero = 0;
const js_uint_one = 1;
const js_plus = (a) => (b) => a + b;
const js_uint_plus = (a) => (b) => a + b;
const js_forget_bound = (n) => (x) => x;
const js_zero_or_pos = (A) => (zeroCase) => (posCase) => (i) =>
  i === 0 ? zeroCase() : posCase(i - 1);
const js_bounded_uint_zero = (n) => 0;
const js_bounded_uint_inc = (n) => (x) => x + 1;
const js_bounded_zero_or_pos = (A) => (zeroCase) => (posCase) => (n) => (i) =>
  i === 0 ? zeroCase(n) : posCase(n)(i - 1);
const js_minus = (a) => (b) => a - b;
const js_times = (a) => (b) => a * b;
const js_uint_times = (a) => (b) => a * b;
const js_div = (a) => (b) => a / b;
const js_mod = (a) => (b) => a % b;
const js_uint_mod = (a) => (b) => a % b;
const js_pow = (a) => (b) => Math.pow(a, b);
const js_uint_pow = (a) => (b) => Math.pow(a, b);
const js_neg = (a) => -a;

// Comparison operations
const js_eq = (A) => (B) => (a) => (b) => a == b;
const js_eqq = (A) => (B) => (a) => (b) => a === b;
const js_neq = (A) => (B) => (a) => (b) => a != b;
const js_neqq = (A) => (B) => (a) => (b) => a !== b;
const js_lt = (a) => (b) => a < b;
const js_lte = (a) => (b) => a <= b;
const js_gt = (a) => (b) => a > b;
const js_gte = (a) => (b) => a >= b;

// Boolean operations
const js_and = (a) => (b) => a && b;
const js_or = (a) => (b) => a || b;
const js_not = (a) => !a;

// Error handling
const js_panic = (T) => (msg) => {
  throw new Error(msg);
};

// IO Monad (CPS style)
const IO = (A) => (f) => f;
const io_return = (A) => (x) => (k) => x;
const io_bind = (A) => (B) => (ma) => (f) => (k) => ma((a) => f(a)(k));

// Unsafe IO execution
const unsafe_io = (A) => (io) => {
  let result;
  io((x) => {
    result = x;
  });
  return result;
};

// JS IO operations
const js_console_log = (T) => (x) => (k) => {
  console.log(x);
  k();
};

// JS Buffer operations
const JsBuffer = null;
const JsBufferMod = (A) => (f) => f;

const js_buffer_bind = (A) => (B) => (ma) => (f) => (buf) => {
  const [newBuf, a] = ma(buf);
  return f(a)(newBuf);
};

const js_buffer_return = (A) => (x) => (buf) => [buf, x];

const js_buffer_get = (buf) => [buf, buf];

const js_buffer_set = (newBuf) => () => [newBuf, undefined];

const js_buffer_empty = Buffer.alloc(0);

const js_buffer_run = (A) => (buf) => (mod) => mod(buf);

const js_buffer_alloc = (byteLength) => Buffer.alloc(byteLength);

const js_buffer_byte_length = (buf) => buf.byteLength;

const js_buffer_copy =
  (source) => (sourceStart) => (sourceEnd) => (start) => (buf) => {
    source.copy(buf, start, sourceStart, sourceEnd);
    return [buf, undefined];
  };

const js_buffer_write_uint16_be = (value) => (offset) => (buf) => {
  buf.writeUInt16BE(value, offset);
  return [buf, undefined];
};

const js_buffer_write_uint8 = (value) => (offset) => (buf) => {
  buf.writeUInt8(value, offset);
  return [buf, undefined];
};

const js_buffer_read_uint16_be = (buffer) => (offset) =>
  buffer.readUInt16BE(offset);

const js_buffer_read_uint8 = (buffer) => (offset) => buffer.readUInt8(offset);

const js_buffer_subarray = (buffer) => (start) => (end) =>
  buffer.subarray(start, end);

// Unsafe operations
const unsafe_cast = (A) => (B) => (x) => x;
const unsafe_complete = (T) => (E) => (t) => (u) => (h) => h;

const js_bound_trust_me = (n) => (x) => x;

const js_assert_defined = (T) => (x) => x;

const prim = (x) => x;

const conjure = (A) => () => null;

const trust_me = (A) => (x) => (y) => null;

var Unit = null;
var tt = [0];
var Sigma = (x15520) => (x15531) => null;
var pair = (x15540) => (x15551) => [0, x15540, x15551];
var dup = (A0) => (a1) => (pair)(a1)(a1);
var fst = (A0) => (B1) => (p2) => (() => {
  switch ((p2)[0]) {
    case 0: return ((a3) => (b4) => a3)((p2)[1])((p2)[2]);
  }
})();
var snd = (_0) => (B1) => (p2) => (() => {
  switch ((p2)[0]) {
    case 0: return ((a3) => (b4) => b4)((p2)[1])((p2)[2]);
  }
})();
var id = (A0) => (a1) => a1;
var if_then_else = (A0) => (b1) => (t2) => (f3) => (js_if_dep)((x784) => A0)(b1)((_4) => (t2)(tt))((_4) => (f3)(tt));
var debug_print = (A0) => (B1) => (a2) => (b3) => (unsafe_io)(B1)((io_bind)(Unit)(B1)((js_console_log)(A0)(a2))((_4) => (io_return)(B1)(b3)));
var Maybe = (x15560) => null;
var nothing = [0];
var just = (x15570) => [1, x15570];
var Either = (x15580) => (x15591) => null;
var left = (x15600) => [0, x15600];
var right = (x15610) => [1, x15610];
var Empty = null;
var VOID = (A0) => (m1) => (() => {
  switch ((m1)[0]) {
    
  }
})();
var Dec = (x15620) => null;
var yes = (x15630) => [0, x15630];
var no = (x15640) => [1, x15640];
var sub = (m0) => (n1) => (js_zero_or_pos)((x1772) => JsUint)((_2) => m0)((x15232) => (js_zero_or_pos)((x1803) => JsUint)((_3) => js_uint_zero)((x15243) => (sub)(x15243)(x15232))(m0))(n1);
var upgrade = (n0) => (k1) => (js_zero_or_pos)((m2) => null)((_2) => (id)((JsBoundedUint)(n0)))((x15252) => (x3) => (js_bounded_uint_inc)((js_uint_plus)(x15252)(n0))((upgrade)(n0)(x15252)(x3)))(k1);
var type = (A0) => (_1) => A0;
var find = (A0) => (p1) => (xs2) => (js_array_switch_l)(A0)((x4093) => (Maybe)(A0))((_3) => nothing)((a3) => (xs4) => (js_if_dep)((x4265) => (Maybe)(A0))((p1)(xs4))((_5) => (just)(xs4))((_5) => (find)(A0)(p1)(a3)))(xs2);
var subst = (A0) => (x1) => (y2) => (P3) => (e4) => (unsafe_cast)(null)(null)((id)((P3)((conjure)(A0))));
var subst_type = (A0) => (B1) => (subst)(null)(A0)(B1)((X2) => X2);
var cong = (A0) => (B1) => (x2) => (y3) => (f4) => (e5) => (unsafe_cast)(JsUndefined)(JsUndefined)(js_undefined);
var sym = (A0) => (x1) => (y2) => (e3) => (unsafe_cast)(JsUndefined)(JsUndefined)(js_undefined);
var z_neq_s = (n0) => (p1) => (subst)(JsUint)(js_uint_zero)((js_uint_plus)(js_uint_one)(n0))((n2) => (js_zero_or_pos)((x6433) => null)((_3) => Unit)((x15373) => Empty)(n2))(p1)(tt);
var co_sym = (A0) => (x1) => (y2) => (m3) => (p4) => (m3)((sym)(A0)(y2)(x1)(p4));
var s_inj = (n0) => (m1) => (e2) => (subst)(JsUint)((js_uint_plus)(js_uint_one)(n0))((js_uint_plus)(js_uint_one)(m1))((x3) => JsUndefined)(e2)(js_undefined);
var s_co_cong = (x0) => (y1) => (m2) => (p3) => (m2)((s_inj)(x0)(y1)(p3));
var nat_eq_dep = (n0) => (m1) => (js_zero_or_pos)((n2) => (Dec)(JsUndefined))((_2) => (js_zero_or_pos)((m3) => (Dec)(JsUndefined))((_3) => (yes)(js_undefined))((x15413) => (no)((z_neq_s)(x15413)))(m1))((x15402) => (js_zero_or_pos)((m3) => (Dec)(JsUndefined))((_3) => (no)((co_sym)(JsUint)(js_uint_zero)((js_uint_plus)(js_uint_one)(x15402))((z_neq_s)(x15402))))((x15433) => (() => {
  switch (((nat_eq_dep)(x15402)(x15433))[0]) {
    case 0: return ((e4) => (yes)((cong)(JsUint)(JsUint)(x15402)(x15433)((n5) => (js_uint_plus)(js_uint_one)(n5))(e4)))(((nat_eq_dep)(x15402)(x15433))[1]);
    case 1: return ((f4) => (no)((s_co_cong)(x15402)(x15433)(f4)))(((nat_eq_dep)(x15402)(x15433))[1]);
  }
})())(m1))(n0);
var dec_to_bool = (A0) => (x8231) => (() => {
  switch ((x8231)[0]) {
    case 0: return ((x8252) => js_true)((x8231)[1]);
    case 1: return ((x8282) => js_false)((x8231)[1]);
  }
})();
var lte = (m0) => (n1) => (js_zero_or_pos)((x8332) => JsBool)((_2) => js_true)((x15442) => (js_zero_or_pos)((x8363) => JsBool)((_3) => js_false)((x15453) => (lte)(x15442)(x15453))(n1))(m0);
var lt = (m0) => (n1) => (js_and)((js_not)((js_eqq)(JsUint)(JsUint)(m0)(n1)))((lte)(m0)(n1));
var bool_eq = (a0) => (b1) => (js_if_dep)((x8402) => JsBool)(a0)((_2) => (js_if_dep)((x8413) => JsBool)(b1)((_3) => js_true)((_3) => js_false))((_2) => (js_if_dep)((x8423) => JsBool)(b1)((_3) => js_false)((_3) => js_true));
var Char = null;
var char_from_num = (x15650) => [0, x15650];
var STRING = null;
var snil = [0];
var scons = (x15660) => (x15671) => [1, x15660, x15671];
var Word = (JsBoundedUint)(65536);
var Byte = (JsBoundedUint)(256);
var word_to_nat = (n0) => (js_forget_bound)(65536)(n0);
var Holds = (b0) => JsUndefined;
var byte_list_length = (l0) => (js_if)(JsUint)((js_eqq)(JsUint)(JsUint)((js_buffer_byte_length)(l0))(0))((_1) => (unsafe_complete)(JsBuffer)((x10032) => JsUint)(l0)(js_buffer_empty)(js_uint_zero))((_1) => (unsafe_complete)(JsBuffer)((x10032) => JsUint)(l0)((fst)(JsBuffer)((x10382) => Unit)((js_buffer_run)(Unit)((js_buffer_alloc)((js_uint_plus)((js_buffer_byte_length)((js_buffer_subarray)(l0)(1)((js_buffer_byte_length)(l0))))(1)))((js_buffer_bind)(Unit)(Unit)((js_buffer_copy)((js_buffer_subarray)(l0)(1)((js_buffer_byte_length)(l0)))(0)((js_buffer_byte_length)((js_buffer_subarray)(l0)(1)((js_buffer_byte_length)(l0))))(1))((_2) => (js_buffer_write_uint8)((js_forget_bound)(256)((js_bound_trust_me)(256)((js_buffer_read_uint8)(l0)(0))))(0)))))((js_uint_plus)(js_uint_one)((byte_list_length)((js_bound_trust_me)(256)((js_buffer_read_uint8)(l0)(0))))));
var byte_vec_length = (n0) => (b1) => n0;
var Reprs = (l0) => (T1) => (js_zero_or_pos)((x13482) => null)((_2) => T1)((x15482) => (Reprs)(x15482)(T1))(l0);
var reprs = (T0) => (l1) => (t2) => (js_zero_or_pos)((l3) => (Reprs)(l3)(T0))((_3) => t2)((x15493) => (reprs)(T0)(x15493)(t2))(l1);
var unreprs = (T0) => (l1) => (js_zero_or_pos)((l2) => null)((_2) => (id)((Reprs)(js_uint_zero)(T0)))((x15502) => (r3) => (unreprs)(T0)(x15502)(r3))(l1);
var repr_subst = (A0) => (B1) => (subst_type)(A0)(B1);
var repr_subst_p_ = (A0) => (B1) => (p2) => (subst_type)(B1)(A0)((sym)(null)(A0)(B1)(p2));
var ReprBy = (T0) => (U1) => (Sigma)(JsUint)((l2) => JsUndefined);
var reprs_subst = (A0) => (B1) => (r2) => (a3) => (() => {
  switch ((r2)[0]) {
    case 0: return ((l4) => (p5) => (subst_type)((Reprs)(l4)(A0))(B1)(p5)((reprs)(A0)(l4)(a3)))((r2)[1])((r2)[2]);
  }
})();
var reprs_subst_p_ = (A0) => (B1) => (r2) => (b3) => (() => {
  switch ((r2)[0]) {
    case 0: return ((l4) => (p5) => (unreprs)(A0)(l4)((subst_type)(B1)((Reprs)(l4)(A0))((sym)(null)((Reprs)(l4)(A0))(B1)(p5))(b3)))((r2)[1])((r2)[2]);
  }
})();
var FizzBuzz = null;
var fizz = [0];
var buzz = [1];
var fizzbuzz = [2];
var fizzbuzz_to_string = (x14970) => (() => {
  switch ((x14970)[0]) {
    case 0: return "nothing!";
    case 1: return ((f1) => (() => {
      switch ((f1)[0]) {
        case 0: return "fizz";
        case 1: return "buzz";
        case 2: return "fizzbuzz";
      }
    })())((x14970)[1]);
  }
})();
var get_fizzbuzz = (n0) => (js_if_dep)((x15031) => (Maybe)(FizzBuzz))((js_eqq)(JsUint)(JsUint)((js_uint_mod)(n0)(15))(0))((_1) => (just)(fizzbuzz))((_1) => (js_if_dep)((x15052) => (Maybe)(FizzBuzz))((js_eqq)(JsUint)(JsUint)((js_uint_mod)(n0)(3))(0))((_2) => (just)(fizz))((_2) => (js_if_dep)((x15073) => (Maybe)(FizzBuzz))((js_eqq)(JsUint)(JsUint)((js_uint_mod)(n0)(5))(0))((_3) => (just)(buzz))((_3) => nothing)));
var repeat = (n0) => (f1) => (js_zero_or_pos)((x15102) => (IO)(Unit))((_2) => (io_return)(Unit)(tt))((x15512) => (io_bind)(Unit)(Unit)((f1)(n0))((_3) => (repeat)(x15512)(f1)))(n0);
var main = (repeat)(323)((n0) => (js_console_log)(STRING)((fizzbuzz_to_string)((get_fizzbuzz)(n0))));
(main)()