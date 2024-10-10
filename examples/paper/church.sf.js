// boot.js
const { Buffer } = require("buffer");

// Type system
const Type = null;

// Equality
const Equal = (x) => (y) => null;

// Primitive types
const JsUnion = null;
const JsNull = null;
const JsUndefined = null;
const JsBool = null;
const JsArray = null;
const JsBigInt = null;
const JsUint = null;
const JsBoundedUint = null;
const JsNumber = null;
const JsString = null;

// Primitive values
const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;

// Conditional
const js_if = (cond) => (thenBranch) => (elseBranch) =>
  cond ? thenBranch() : elseBranch();
const js_if_dep = (b) => (thenBranch) => (elseBranch) =>
  b ? thenBranch() : elseBranch();

// Array operations
const js_empty_array = () => [];
const js_array_extend_l = (x) => (arr) => [x, ...arr];
const js_array_extend_r = (arr) => (x) => [...arr, x];
const js_array_switch_l = (emptyCase) => (nonEmptyCase) => (arr) =>
  arr.length === 0 ? emptyCase() : nonEmptyCase(arr[0])(arr.slice(1));
const js_array_switch_r = (emptyCase) => (nonEmptyCase) => (arr) =>
  arr.length === 0
    ? emptyCase()
    : nonEmptyCase(arr.slice(0, -1))(arr[arr.length - 1]);
const js_slice = (arr) => (start) => (end) => arr.slice(start, end);
const js_length = (arr) => arr.length;
const js_map = (a) => (fn) => a.map((x, i) => fn([x, i]));
const js_reduce = (fn) => (initial) => (arr) =>
  arr.reduce((acc, val) => fn(acc)(val), initial);
const js_index = (a) => (n) => a[n];

// Number operations
const js_zero = 0;
const js_one = 1;
const js_uint_zero = 0;
const js_uint_one = 1;
const js_plus = (a) => (b) => a + b;
const js_uint_plus = (a) => (b) => a + b;
const js_forget_bound = (x) => x;
const js_zero_or_pos = (zeroCase) => (posCase) => (i) =>
  i === 0 ? zeroCase() : posCase(i - 1);
const js_bounded_uint_zero = 0;
const js_bounded_uint_inc = (x) => x + 1;
const js_bounded_zero_or_pos = (zeroCase) => (posCase) => (n) => (i) =>
  i === 0 ? zeroCase(n) : posCase(n)(i - 1);
const js_minus = (a) => (b) => a - b;
const js_times = (a) => (b) => a * b;
const js_uint_times = (a) => (b) => a * b;
const js_div = (a) => (b) => a / b;
const js_mod = (a) => (b) => a % b;
const js_uint_mod = (a) => (b) => a % b;
const js_uint_div = (a) => (b) => Math.floor(a / b);
const js_pow = (a) => (b) => Math.pow(a, b);
const js_uint_pow = (a) => (b) => Math.pow(a, b);
const js_neg = (a) => -a;

// Comparison operations
const js_eq = (a) => (b) => a == b;
const js_eqq = (a) => (b) => a === b;
const js_neq = (a) => (b) => a != b;
const js_neqq = (a) => (b) => a !== b;
const js_lt = (a) => (b) => a < b;
const js_lte = (a) => (b) => a <= b;
const js_gt = (a) => (b) => a > b;
const js_gte = (a) => (b) => a >= b;

// Boolean operations
const js_and = (a) => (b) => a && b;
const js_or = (a) => (b) => a || b;
const js_not = (a) => !a;

// Error handling
const js_panic = (msg) => {
  throw new Error(msg);
};

// IO Monad (CPS style)
const IO = (f) => f;
const io_return = (x) => (k) => x;
const io_bind = (ma) => (f) => (k) => ma((a) => f(a)(k));

// Unsafe IO execution
const unsafe_io = (io) => {
  let result;
  io((x) => {
    result = x;
  });
  return result;
};

// JS IO operations
const js_console_log = (x) => (k) => {
  console.log(x);
  k();
};

// JS Buffer operations
const JsBuffer = null;
const JsBufferMod = (f) => f;

const js_buffer_bind = (ma) => (f) => (buf) => {
  const [newBuf, a] = ma(buf);
  return f(a)(newBuf);
};

const js_buffer_return = (x) => (buf) => [buf, x];

const js_buffer_get = (buf) => [buf, buf];

const js_buffer_set = (newBuf) => () => [newBuf, undefined];

const js_buffer_empty = Buffer.alloc(0);

const js_buffer_run = (buf) => (mod) => mod(buf);

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
const unsafe_cast = (x) => x;
const unsafe_complete = (h) => h;

const js_bound_trust_me = (x) => x;

const js_assert_defined = (x) => x;

const prim = (x) => x;

const conjure = null;

const trust_me = null;

var Unit = null;
var tt = [0];
var Sigma = (A0) => (B1) => null;
var pair = (x18590) => (x18601) => [0, x18590, x18601];
var dup = (a1) => (pair)(a1)(a1);
var fst = (x322) => (() => {
  switch ((x322)[0]) {
    case 0: return ((a3) => (x374) => a3)((x322)[1])((x322)[2]);
  }
})();
var snd = (p2) => (() => {
  switch ((p2)[0]) {
    case 0: return ((a3) => (b4) => b4)((p2)[1])((p2)[2]);
  }
})();
var id = (a1) => a1;
var if_then_else = (b1) => (t2) => (f3) => (js_if_dep)(b1)((_4) => (t2)(tt))((_4) => (f3)(tt));
var debug_print = (a2) => (b3) => (unsafe_io)((io_bind)((js_console_log)(a2))((_4) => (io_return)(b3)));
var Maybe = (A0) => null;
var nothing = [0];
var just = (x18610) => [1, x18610];
var is_just = (x1311) => (() => {
  switch ((x1311)[0]) {
    case 0: return js_false;
    case 1: return ((x1352) => js_true)((x1311)[1]);
  }
})();
var Either = (L0) => (R1) => null;
var left = (x18620) => [0, x18620];
var right = (x18630) => [1, x18630];
var Empty = null;
var VOID = (m1) => (() => {
  switch ((m1)[0]) {
    
  }
})();
var Dec = (A0) => null;
var yes = (x18640) => [0, x18640];
var no = (x18650) => [1, x18650];
var sub = (m0) => (n1) => (js_zero_or_pos)((_2) => m0)((x2) => (js_zero_or_pos)((_3) => js_uint_zero)((x3) => (sub)(x3)(x2))(m0))(n1);
var upgrade = (k1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (x3) => (js_bounded_uint_inc)((upgrade)(x2)(x3)))(k1);
var find = (p1) => (xs2) => (js_array_switch_l)((_3) => nothing)((a3) => (xs4) => (js_if_dep)((p1)(xs4))((_5) => (just)(xs4))((_5) => (find)(p1)(a3)))(xs2);
var subst = (e4) => (unsafe_cast)((a5) => a5);
var subst_type = subst;
var cong = (f4) => (e5) => (unsafe_cast)(js_undefined);
var sym = (e3) => (unsafe_cast)(js_undefined);
var z_neq_s = (p1) => (subst)(p1)(tt);
var co_sym = (m3) => (p4) => (m3)((sym)(p4));
var s_inj = (e2) => (subst)(e2)(js_undefined);
var s_co_cong = (m2) => (p3) => (m2)((s_inj)(p3));
var dec_to_bool = (x8261) => (() => {
  switch ((x8261)[0]) {
    case 0: return ((x8282) => js_true)((x8261)[1]);
    case 1: return ((x8312) => js_false)((x8261)[1]);
  }
})();
var lte = (m0) => (n1) => (js_zero_or_pos)((_2) => js_true)((x2) => (js_zero_or_pos)((_3) => js_false)((x3) => (lte)(x2)(x3))(n1))(m0);
var lt = (m0) => (n1) => (js_and)((js_not)((js_eqq)(m0)(n1)))((lte)(m0)(n1));
var bool_eq = (a0) => (b1) => (js_if_dep)(a0)((_2) => (js_if_dep)(b1)((_3) => js_true)((_3) => js_false))((_2) => (js_if_dep)(b1)((_3) => js_false)((_3) => js_true));
var Char = null;
var utf32_code = (x18660) => [0, x18660];
var char_eq = (c10) => (c21) => (() => {
  switch ((c10)[0]) {
    case 0: return ((f12) => (() => {
      switch ((c21)[0]) {
        case 0: return ((f23) => (js_eqq)(f12)(f23))((c21)[1]);
      }
    })())((c10)[1]);
  }
})();
var STRING = null;
var snil = [0];
var scons = (x18670) => (x18681) => [1, x18670, x18681];
var string_eq = (s10) => (s21) => (() => {
  switch ((s10)[0]) {
    case 0: return (() => {
      switch ((s21)[0]) {
        case 0: return js_true;
        case 1: return ((x10152) => (x10163) => js_false)((s21)[1])((s21)[2]);
      }
    })();
    case 1: return ((c12) => (s1_p_3) => (() => {
      switch ((s21)[0]) {
        case 0: return js_false;
        case 1: return ((c24) => (s2_p_5) => (js_and)((char_eq)(c12)(c24))((string_eq)(s1_p_3)(s2_p_5)))((s21)[1])((s21)[2]);
      }
    })())((s10)[1])((s10)[2]);
  }
})();
var Word = JsBoundedUint;
var Byte = JsBoundedUint;
var ascii_eq = (a10) => (a21) => (unsafe_complete)((unsafe_complete)((js_eqq)(a10)(a21)));
var word_to_nat = (n0) => (js_forget_bound)(n0);
var Holds = JsUndefined;
var determine = (x0) => (js_if_dep)(x0)((_1) => (just)(js_undefined))((_1) => nothing);
var byte_vec_lookup = (s2) => (l3) => (d4) => (js_array_switch_l)((_5) => (d4)(tt))((a5) => (xs6) => (() => {
  var x12277 = xs6;
  return (() => {
    switch ((x12277)[0]) {
      case 0: return ((k8) => (v9) => (if_then_else)((js_buffer_eq)((fst)(s2))((fst)(k8)))((_10) => (v9)(tt))((_10) => (byte_vec_lookup)(s2)(a5)(d4)))((x12277)[1])((x12277)[2]);
    }
  })();
})())(l3);
var panic = (a1) => (unsafe_io)((io_bind)((js_console_log)(a1))((_2) => (js_exit)(js_one)));
var reprs = (l1) => (t2) => (js_zero_or_pos)((_3) => t2)((x3) => (reprs)(x3)(t2))(l1);
var unreprs = (l1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (r3) => (unreprs)(x2)(r3))(l1);
var repr_subst = subst_type;
var repr_subst_p_ = (p2) => (subst_type)((sym)(p2));
var ReprBy = (Sigma)(JsUint)(JsUndefined);
var reprs_subst = (r2) => (a3) => (() => {
  var x17154 = r2;
  return (() => {
    switch ((x17154)[0]) {
      case 0: return ((l5) => (p6) => (subst_type)(p6)((reprs)(l5)(a3)))((x17154)[1])((x17154)[2]);
    }
  })();
})();
var reprs_subst_p_ = (r2) => (b3) => (() => {
  var x17584 = r2;
  return (() => {
    switch ((x17584)[0]) {
      case 0: return ((l5) => (p6) => (unreprs)(l5)((subst_type)((sym)(p6))(b3)))((x17584)[1])((x17584)[2]);
    }
  })();
})();
var Vec = (T0) => null;
var vec_nil = [0];
var vec_cons = (x18690) => (x18701) => [1, x18690, x18701];
var vec_length = (n1) => (_2) => n1;
var boo = (() => {
  var v0 = (vec_cons)("a")((vec_cons)("b")(vec_nil));
  var n1 = (vec_length)((js_uint_plus)(js_uint_one)((js_uint_plus)(js_uint_one)(0)))(v0);
  return (io_return)(tt);
})();
(main)()