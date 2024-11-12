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
const js_empty_array = [];
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
  return k;
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

var debug_print = (a2) => (b3) => (unsafe_io)((io_bind)((js_console_log)(a2))((_4) => (io_return)(b3)));
var print = js_console_log;
var is_just = (x1941) => (() => {
  switch ((x1941)[0]) {
    case "nothing": return js_false;
    case "just": return ((x1982) => js_true)((x1941)[1]);
  }
})();
var VOID = (m1) => null;
var sub = (m0) => (n1) => (js_zero_or_pos)((_2) => m0)((x2) => (js_zero_or_pos)((_3) => js_uint_zero)((x3) => (sub)(x3)(x2))(m0))(n1);
var upgrade = (k1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (x3) => (js_bounded_uint_inc)((upgrade)(x2)(x3)))(k1);
var find = (p1) => (xs2) => (js_array_switch_l)((_3) => "nothing")((a3) => (xs4) => (js_if_dep)((p1)(a3))((_5) => ["just", a3])((_5) => (find)(p1)(xs4)))(xs2);
var cong = [];
var sym = [];
var uip = trust_me;
var equality_is_prop = uip;
var z_neq_s = ((a2) => a2)([]);
var co_sym = (m3) => m3;
var s_inj = ((a3) => a3)([]);
var s_co_cong = (m2) => m2;
var dec_to_bool = (x8391) => (() => {
  switch ((x8391)[0]) {
    case "yes": return ((x8412) => js_true)((x8391)[1]);
    case "no": return ((x8442) => js_false)((x8391)[1]);
  }
})();
var lte = (m0) => (n1) => (js_zero_or_pos)((_2) => js_true)((x2) => (js_zero_or_pos)((_3) => js_false)((x3) => (lte)(x2)(x3))(n1))(m0);
var lt = (m0) => (n1) => (js_and)((js_not)((js_eqq)(m0)(n1)))((lte)(m0)(n1));
var bool_eq = (a0) => (b1) => (js_if_dep)(a0)((_2) => (js_if_dep)(b1)((_3) => js_true)((_3) => js_false))((_2) => (js_if_dep)(b1)((_3) => js_false)((_3) => js_true));
var char_eq = (c10) => (c21) => ((f12) => ((f23) => (js_eqq)(f12)(f23))(c21))(c10);
var string_eq = (s10) => (s21) => (() => {
  switch ((s10)[0]) {
    case "snil": return (() => {
      switch ((s21)[0]) {
        case "snil": return js_true;
        case "scons": return ((x9842) => (x9853) => js_false)((s21)[1])((s21)[2]);
      }
    })();
    case "scons": return ((c12) => (s1_p_3) => (() => {
      switch ((s21)[0]) {
        case "snil": return js_false;
        case "scons": return ((c24) => (s2_p_5) => (js_and)((char_eq)(c12)(c24))((string_eq)(s1_p_3)(s2_p_5)))((s21)[1])((s21)[2]);
      }
    })())((s10)[1])((s10)[2]);
  }
})();
var ascii_eq = (a10) => (a21) => (unsafe_complete)((unsafe_complete)((js_eqq)(a10)(a21)));
var word_to_nat = (n0) => (js_forget_bound)(n0);
var determine = (x0) => (js_if_dep)(x0)((_1) => ["just", []])((_1) => "nothing");
var byte_vec_lookup = (s2) => (l3) => (d4) => (js_array_switch_l)((_5) => (d4)([]))((a5) => (xs6) => (() => {
  var x11217 = a5;
  return ((k8) => (v9) => (js_if_dep)((js_buffer_eq)(((a10) => v9)(s2))(((a10) => v9)(k8)))((_10) => (v9)([]))((_10) => (byte_vec_lookup)(s2)(xs6)(d4)))((x11217)[0])((x11217)[1]);
})())(l3);
var panic = (a1) => (unsafe_io)((io_bind)((js_console_log)(a1))((_2) => (js_exit)(js_one)));
var reprs = (l1) => (t2) => (js_zero_or_pos)((_3) => t2)((x3) => (reprs)(x3)(t2))(l1);
var unreprs = (l1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (r3) => (unreprs)(x2)(r3))(l1);
var repr_subst = (a3) => a3;
var repr_subst_p_ = (a3) => a3;
var reprs_subst = (r2) => (a3) => (() => {
  var x15714 = r2;
  return ((l5) => (p6) => ((a7) => a7)((reprs)(l5)(a3)))((x15714)[0])((x15714)[1]);
})();
var reprs_subst_p_ = (r2) => (b3) => (() => {
  var x16064 = r2;
  return ((l5) => (p6) => (unreprs)(l5)(((a7) => a7)(b3)))((x16064)[0])((x16064)[1]);
})();
var list_is_functor = null;
var list_is_monad = null;
var main = (() => {
  var mo0 = (m0) => (() => {
    switch ((m0)[0]) {
      case "nothing": return "nothing";
      case "just": return ((a1) => (() => {
        var x2 = a1;
        var x_p_3 = (js_uint_plus)(3)(x2);
        return ["just", x_p_3];
      })())((m0)[1]);
    }
  })();
  return (() => {
    switch (((mo0)(["just", 3]))[0]) {
      case "nothing": return (io_return)([]);
      case "just": return ((t1) => (print)(t1))(((mo0)(["just", 3]))[1]);
    }
  })();
})();
(main)()