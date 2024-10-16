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

var tt = [0];
var pair = (x32190) => (x32201) => [0, x32190, x32201];
var refl = [0];
var debug_print = (a2) => (b3) => (unsafe_io)((io_bind)((js_console_log)(a2))((_4) => (io_return)(b3)));
var nothing = [0];
var just = (x32210) => [1, x32210];
var is_just = (x1311) => (() => {
  switch ((x1311)[0]) {
    case 0: return js_false;
    case 1: return ((x1352) => js_true)((x1311)[1]);
  }
})();
var left = (x32220) => [0, x32220];
var right = (x32230) => [1, x32230];
var VOID = (m1) => null;
var yes = (x32240) => [0, x32240];
var no = (x32250) => [1, x32250];
var sub = (m0) => (n1) => (js_zero_or_pos)((_2) => m0)((x2) => (js_zero_or_pos)((_3) => js_uint_zero)((x3) => (sub)(x3)(x2))(m0))(n1);
var upgrade = (k1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (x3) => (js_bounded_uint_inc)((upgrade)(x2)(x3)))(k1);
var find = (p1) => (xs2) => (js_array_switch_l)((_3) => nothing)((a3) => (xs4) => (js_if_dep)((p1)(xs4))((_5) => (just)(xs4))((_5) => (find)(p1)(a3)))(xs2);
var cong = refl;
var sym = refl;
var uip = trust_me;
var equality_is_prop = uip;
var z_neq_s = ((a2) => a2)(tt);
var co_sym = (m3) => m3;
var s_inj = ((a3) => a3)(refl);
var s_co_cong = (m2) => m2;
var dec_to_bool = (x9111) => (() => {
  switch ((x9111)[0]) {
    case 0: return ((x9132) => js_true)((x9111)[1]);
    case 1: return ((x9162) => js_false)((x9111)[1]);
  }
})();
var lte = (m0) => (n1) => (js_zero_or_pos)((_2) => js_true)((x2) => (js_zero_or_pos)((_3) => js_false)((x3) => (lte)(x2)(x3))(n1))(m0);
var lt = (m0) => (n1) => (js_and)((js_not)((js_eqq)(m0)(n1)))((lte)(m0)(n1));
var bool_eq = (a0) => (b1) => (js_if_dep)(a0)((_2) => (js_if_dep)(b1)((_3) => js_true)((_3) => js_false))((_2) => (js_if_dep)(b1)((_3) => js_false)((_3) => js_true));
var utf32_code = (x32260) => [0, x32260];
var char_eq = (c10) => (c21) => (() => {
  switch ((c10)[0]) {
    case 0: return ((f12) => (() => {
      switch ((c21)[0]) {
        case 0: return ((f23) => (js_eqq)(f12)(f23))((c21)[1]);
      }
    })())((c10)[1]);
  }
})();
var snil = [0];
var scons = (x32270) => (x32281) => [1, x32270, x32281];
var string_eq = (s10) => (s21) => (() => {
  switch ((s10)[0]) {
    case 0: return (() => {
      switch ((s21)[0]) {
        case 0: return js_true;
        case 1: return ((x10802) => (x10813) => js_false)((s21)[1])((s21)[2]);
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
var Holds = Equal;
var determine = (x0) => (js_if_dep)(x0)((_1) => (just)(refl))((_1) => nothing);
var byte_vec_lookup = (s2) => (l3) => (d4) => (js_array_switch_l)((_5) => (d4)(tt))((a5) => (xs6) => (() => {
  var x12927 = xs6;
  return (() => {
    switch ((x12927)[0]) {
      case 0: return ((k8) => (v9) => (js_if_dep)((js_buffer_eq)((() => {
        switch ((s2)[0]) {
          case 0: return ((a10) => (x3711) => a10)((s2)[1])((s2)[2]);
        }
      })())((() => {
        switch ((k8)[0]) {
          case 0: return ((a10) => (x3711) => a10)((k8)[1])((k8)[2]);
        }
      })()))((_10) => (v9)(tt))((_10) => (byte_vec_lookup)(s2)(a5)(d4)))((x12927)[1])((x12927)[2]);
    }
  })();
})())(l3);
var panic = (a1) => (unsafe_io)((io_bind)((js_console_log)(a1))((_2) => (js_exit)(js_one)));
var reprs = (l1) => (t2) => (js_zero_or_pos)((_3) => t2)((x3) => (reprs)(x3)(t2))(l1);
var unreprs = (l1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (r3) => (unreprs)(x2)(r3))(l1);
var repr_subst = (a3) => a3;
var repr_subst_p_ = (a3) => a3;
var ReprBy = (Sigma)(JsUint)(Equal);
var reprs_subst = (r2) => (a3) => (() => {
  var x17824 = r2;
  return (() => {
    switch ((x17824)[0]) {
      case 0: return ((l5) => (p6) => ((a7) => a7)((reprs)(l5)(a3)))((x17824)[1])((x17824)[2]);
    }
  })();
})();
var reprs_subst_p_ = (r2) => (b3) => (() => {
  var x18254 = r2;
  return (() => {
    switch ((x18254)[0]) {
      case 0: return ((l5) => (p6) => (unreprs)(l5)(((a7) => a7)(b3)))((x18254)[1])((x18254)[2]);
    }
  })();
})();
var vec_length = (n1) => (_2) => n1;
var ri_pair = (x32290) => [0, x32290];
var vec_index = (v2) => (() => {
  var l3 = (() => {
    switch ((v2)[0]) {
      case 0: return ((a3) => v2)((v2)[1]);
    }
  })();
  return ((a5) => a5)((js_array_switch_l)((_5) => (js_zero_or_pos)((_6) => ((a8) => a8)((i8) => null))((x6) => null)(n1))((a5) => (xs6) => (js_zero_or_pos)((_7) => null)((x7) => ((a9) => a9)((i9) => (js_bounded_zero_or_pos)(xs6)((f11) => (() => {
    var p_p_13 = s_inj;
    return (vec_index)(x7)(((a14) => a14)(n10));
  })())(i9)))(n1))(l3));
})();
var safe_index = (l2) => (i4) => (vec_index)((ri_pair)(l2))(i4);
var main = (() => {
  var v0 = (ri_pair)((js_array_extend_l)(1)(cong));
  var n1 = (vec_index)(v0)(2);
  return (js_console_log)(n1);
})();
(main)()