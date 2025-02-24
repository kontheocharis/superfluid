// boot.js
const { Buffer } = require("buffer");
const fs = require("fs");

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

const js_optional_case = (emptyCase) => (nonEmptyCase) => (x) => {
  if (x === null) {
    return emptyCase;
  }
  return nonEmptyCase(x);
};

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
const js_sort = (cmp) => (a) => [...a].sort((a, b) => cmp(a)(b));
const js_reduce = (fn) => (initial) => (arr) =>
  arr.reduce((acc, val) => fn(acc)(val), initial);
const js_index = (a) => (n) => a[n];
const js_filter = (fn) => (a) => a.filter(fn);

// String operations
const js_string_concat = (a) => (b) => a + b;
const js_string_length = (s) => s.length;
const js_string_index = (s) => (n) => s[n];
const js_string_slice = (s) => (start) => (end) => s.slice(start, end);
const js_string_char_at = (s) => (n) => s.charAt(n);
const js_string_split = (s) => (sep) => s.split(sep);
const js_string_elim = (a) => (f) => (s) => {
  if (s.length === 0) {
    return a;
  }
  const head = s.charAt(0);
  const tail = s.slice(1);
  return f(head)(tail);
};
const js_string_from_char_code = (code) => String.fromCharCode(code);

// Number operations
const js_zero = 0;
const js_one = 1;
const js_uint_zero = 0;
const js_uint_one = 1;
const js_plus = (a) => (b) => a + b;
const js_uint_plus = (a) => (b) => a + b;
const js_uint_minus = (a) => (b) => a - b;
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

const js_parse_uint = (s) => {
  const x = parseInt(s, 10);
  if (x >= 0 && Number.isInteger(x)) {
    return x;
  }
  return null;
};

// Boolean operations
const js_and = (a) => (b) => a && b;
const js_or = (a) => (b) => a || b;
const js_not = (a) => !a;

// IO Monad (CPS style)
const IO = (f) => f;
const io_return = (x) => (k) => k(x);
const io_effect = (x) => (k) => k(x());
const io_bind = (ma) => (f) => (k) => ma((a) => f(a)(k));

// Error handling
const js_panic = (msg) =>
  io_effect(() => {
    throw new Error(msg);
  });

const js_exit = (code) =>
  io_effect(() => {
    process.exit(code);
  });

// Unsafe IO execution
const unsafe_io = (io) => {
  let result;
  io((x) => {
    result = x;
  });
  return result;
};

// JS IO operations
const js_console_log = (x) =>
  io_effect(() => {
    return console.log(x);
  });
const js_read_file = (file) =>
  io_effect(() => {
    return fs.readFileSync(file, "utf8");
  });

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

const js_to_string = (x) => String(x);

const prim = (x) => x;

const conjure = null;

const trust_me = null;

// Cells

const Cell = (value) => value;

const cell = (value) =>
  io_effect(() => ({
    value,
  }));

const get_cell = (cell) => io_effect(() => cell.value);

const set_cell = (cell) => (value) => {
  return io_effect(() => {
    cell.value = value;
  });
};

var transport_repr = (x2) => (unsafe_cast)(x2);
var transport_unrepr = (x2) => (unsafe_cast)(x2);
var debug_print = (a2) => (b3) => (unsafe_io)((io_bind)((js_console_log)(a2))((_4) => (io_return)(b3)));
var is_just = (x1981) => (() => {
  var subject2 = x1981;
  return (() => {
    switch ((subject2)[0]) {
      case "nothing": return js_false;
      case "just": return ((x2022) => js_true)((subject2)[1]);
    }
  })();
})();
var VOID = (m1) => null;
var upgrade = (k1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (x3) => (js_bounded_uint_inc)((upgrade)(x2)(x3)))(k1);
var find = (p1) => (xs2) => (js_array_switch_l)((_3) => ["nothing"])((a3) => (xs4) => (js_if_dep)((p1)(a3))((_5) => ["just", a3])((_5) => (find)(p1)(xs4)))(xs2);
var cong = [];
var sym = [];
var uip = trust_me;
var equality_is_prop = uip;
var z_neq_s = ((a2) => a2)([]);
var co_sym = (m3) => m3;
var s_inj = ((a3) => a3)([]);
var s_co_cong = (m2) => m2;
var dec_to_bool = (x8711) => (() => {
  var subject2 = x8711;
  return (() => {
    switch ((subject2)[0]) {
      case "yes": return ((x8732) => js_true)((subject2)[1]);
      case "no": return ((x8762) => js_false)((subject2)[1]);
    }
  })();
})();
var bool_eq = (a0) => (b1) => (js_if_dep)(a0)((_2) => (js_if_dep)(b1)((_3) => js_true)((_3) => js_false))((_2) => (js_if_dep)(b1)((_3) => js_false)((_3) => js_true));
var nat_cmp = (a0) => (b1) => (js_if_dep)((js_eqq)(a0)(b1))((_2) => ["ord-eq"])((_2) => (js_if_dep)((js_lt)(a0)(b1))((_3) => ["ord-lt"])((_3) => ["ord-gt"]));
var sort = (cmp1) => (l2) => (() => {
  var cmp_p_3 = (a3) => (b4) => (() => {
    var subject5 = (cmp1)(a3)(b4);
    return (() => {
      switch ((subject5)[0]) {
        case "ord-lt": return js_one;
        case "ord-eq": return js_zero;
        case "ord-gt": return (js_minus)(js_zero)(js_one);
      }
    })();
  })();
  return (js_sort)(cmp_p_3)(l2);
})();
var char_eq = (c10) => (c21) => (unsafe_cast)((unsafe_cast)((js_eqq)(c10)(c21)));
var string_eq = (s10) => (s21) => (js_string_elim)((js_string_elim)(js_true)((l2) => (m3) => js_false)(s21))((l2) => (m3) => (js_string_elim)(js_false)((l4) => (m5) => (js_and)((char_eq)(l2)(l4))((string_eq)(m3)(m5)))(s21))(s10);
var string_split = (a0) => (b1) => (transport_unrepr)((js_string_split)(a0)(b1));
var string_length = (s0) => (js_string_length)(s0);
var string_index = (s0) => (n1) => (js_if_dep)((js_lt)(n1)((string_length)(s0)))((_2) => ["just", (js_string_char_at)(s0)(n1)])((_2) => ["nothing"]);
var string_concat = (a0) => (b1) => (js_string_concat)(a0)(b1);
var string_slice = (s0) => (start1) => (end2) => (js_string_slice)(s0)(start1)(end2);
var parse_nat = (s0) => (js_optional_case)(["nothing"])((x1) => ["just", x1])((js_parse_uint)(s0));
var show_nat = (n0) => (js_to_string)(n0);
var ascii_eq = (a10) => (a21) => (unsafe_complete)((unsafe_complete)((js_eqq)(a10)(a21)));
var word_to_nat = (n0) => (js_forget_bound)(n0);
var determine = (x0) => (js_if_dep)(x0)((_1) => ["just", []])((_1) => ["nothing"]);
var byte_vec_lookup = (s2) => (l3) => (d4) => (js_array_switch_l)((_5) => (d4)([]))((a5) => (xs6) => (() => {
  var x12317 = a5;
  return (() => {
    var subject8 = x12317;
    return ((k8) => (v9) => (js_if_dep)((js_buffer_eq)((() => {
      var subject10 = s2;
      return ((a10) => v9)(subject10);
    })())((() => {
      var subject10 = k8;
      return ((a10) => v9)(subject10);
    })()))((_10) => (v9)([]))((_10) => (byte_vec_lookup)(s2)(xs6)(d4)))((subject8)[0])((subject8)[1]);
  })();
})())(l3);
var panic = (a1) => (unsafe_io)((io_bind)((js_console_log)(a1))((_2) => (js_exit)(js_one)));
var reprs = (l1) => (t2) => (js_zero_or_pos)((_3) => t2)((x3) => (reprs)(x3)(t2))(l1);
var unreprs = (l1) => (js_zero_or_pos)((_2) => (a3) => a3)((x2) => (r3) => (unreprs)(x2)(r3))(l1);
var repr_subst = (a3) => a3;
var repr_subst_p_ = (a3) => a3;
var reprs_subst = (r2) => (a3) => (() => {
  var x16774 = r2;
  return (() => {
    var subject5 = x16774;
    return ((l5) => (p6) => ((a7) => a7)((reprs)(l5)(a3)))((subject5)[0])((subject5)[1]);
  })();
})();
var reprs_subst_p_ = (r2) => (b3) => (() => {
  var x17124 = r2;
  return (() => {
    var subject5 = x17124;
    return ((l5) => (p6) => (unreprs)(l5)(((a7) => a7)(b3)))((subject5)[0])((subject5)[1]);
  })();
})();
var THROW = (s1) => (js_panic)(s1);
var modify_cell = (cell1) => (f2) => (io_bind)((get_cell)(cell1))((x3) => (set_cell)(cell1)((f2)(x3)));
var nat_fold_range = (x17851) => (() => {
  var subject2 = x17851;
  return ((start2) => (end3) => (init4) => (f5) => (js_if_dep)((js_lt)(start2)(end3))((_6) => (nat_fold_range)([(js_uint_plus)(js_uint_one)(start2), end3])((f5)(start2)(init4))(f5))((_6) => init4))((subject2)[0])((subject2)[1]);
})();
var sum_of_divisors = (n0) => (nat_fold_range)([1, (js_uint_plus)(js_uint_one)((js_uint_div)(n0)(2))])(0)((i1) => (acc2) => (js_if_dep)((js_eqq)((js_uint_mod)(n0)(i1))(0))((_3) => (js_uint_plus)(acc2)(i1))((_3) => acc2));
var is_amicable_pair = (a0) => (b1) => (() => {
  var sum_a2 = (sum_of_divisors)(a0);
  var sum_b3 = (sum_of_divisors)(b1);
  return (() => {
    var subject4 = (() => {
      var res4 = (js_eqq)(sum_a2)(b1);
      return (js_if_dep)(res4)((_5) => ["yes", trust_me])((_5) => ["no", conjure]);
    })();
    return (() => {
      switch ((subject4)[0]) {
        case "yes": return ((p14) => (() => {
          var subject5 = (() => {
            var res5 = (js_eqq)(sum_b3)(a0);
            return (js_if_dep)(res5)((_6) => ["yes", trust_me])((_6) => ["no", conjure]);
          })();
          return (() => {
            switch ((subject5)[0]) {
              case "yes": return ((p25) => ["just", [a0, b1]])((subject5)[1]);
              case "no": return ((x18615) => ["nothing"])((subject5)[1]);
            }
          })();
        })())((subject4)[1]);
        case "no": return ((x18694) => ["nothing"])((subject4)[1]);
      }
    })();
  })();
})();
var main = (() => {
  var subject0 = (is_amicable_pair)(284)(220);
  return (() => {
    switch ((subject0)[0]) {
      case "nothing": return (io_return)((debug_print)("Not amicable!")([]));
      case "just": return ((x18760) => (io_return)((debug_print)("Amicable!")([])))((subject0)[1]);
    }
  })();
})();
(main)((x) => x)