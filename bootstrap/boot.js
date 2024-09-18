const { Buffer } = require("node:buffer");
const prompt = require("prompt-sync")();

const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;
const js_zero = 0;
const js_one = 1;

const js_plus = (a, b) => a + b;
const js_minus = (a, b) => a - b;
const js_times = (a, b) => a * b;
const js_div = (a, b) => a / b;
const js_mod = (a, b) => a % b;
const js_pow = (a, b) => a ** b;
const js_neg = (a) => -a;

const js_eq = (a, b) => a == b;
const js_eqq = (a, b) => a === b;
const js_neq = (a, b) => a != b;
const js_neqq = (a, b) => a !== b;
const js_lt = (a, b) => a < b;
const js_lte = (a, b) => a <= b;
const js_gt = (a, b) => a > b;
const js_gte = (a, b) => a >= b;

const js_and = (a, b) => a && b;
const js_or = (a, b) => a || b;
const js_not = (a) => !a;

const js_cond = (c, t, f) => (c ? t : f);
const js_typeof = (e) => typeof e;
const js_lazy = (e) => () => e;

const js_app = (f, as) => f(...as);
const js_multi_app = (f, as) => f(...as);

const js_switch = (e, cs) => {
  for (const [c, s] of cs) {
    if (e === c) return s;
  }
};

const js_obj = (ps) => {
  const obj = {};
  for (const [s, e] of ps) {
    obj[s] = e;
  }
  return obj;
};

const js_invoke = (e) => e();

const js_empty_array = [];

const js_array_extend_l = (a, b) => [a, ...b];
const js_array_extend_r = (a, b) => [...a, b];

const js_length = (a) => a.length;

const js_slice = (a, b, c) => a.slice(b, c);

const js_fold = (f, i, a) => a.reduce(f, i);

const js_map = (f, a) => a.map(f);
