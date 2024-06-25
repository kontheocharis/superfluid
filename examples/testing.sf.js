const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const fib = (n) => ((n) === (0)) ? (0) : ((((n) - (1)) === (0)) ? ((1) + (0)) : (((fib)((n) - (1))) + ((fib)(((n) - (1)) - (1)))));
const nat_eq = (n) => (m) => ((n) === (0)) ? (((m) === (0)) ? (true) : (((m) === (0)) ? (true) : (false))) : (((m) === (0)) ? (false) : (((nat_eq)((n) - (1)))((m) - (1))));
const sub = (e) => (n) => (t) => (() => {
  switch ((e)[0]) {
    case "var": return (((nat_eq)(n))((e)[(1) + (0)])) ? (t) : (["var", (e)[(1) + (0)]]);
    case "app": return ["app", (((sub)((e)[(1) + (0)]))(n))(t), (((sub)((e)[(1) + ((1) + (0))]))(n))(t)];
    case "lam": return ["lam", (((sub)((e)[(1) + (0)]))((1) + (n)))(t)];
  }
})();
const eval = (e) => (() => {
  switch ((e)[0]) {
    case "var": return ["var", (e)[(1) + (0)]];
    case "app": return (() => {
      switch (((eval)((e)[(1) + (0)]))[0]) {
        case "lam": return (eval)((((sub)(((eval)((e)[(1) + (0)]))[(1) + (0)]))(0))((e)[(1) + ((1) + (0))]));
        case "app": return ["app", ["app", ((eval)((e)[(1) + (0)]))[(1) + (0)], ((eval)((e)[(1) + (0)]))[(1) + ((1) + (0))]], (e)[(1) + ((1) + (0))]];
        case "var": return ["app", ["var", ((eval)((e)[(1) + (0)]))[(1) + (0)]], (eval)((e)[(1) + ((1) + (0))])];
      }
    })();
    case "lam": return ["lam", (eval)((e)[(1) + (0)])];
  }
})();
const identity = ["lam", ["var", 0]];
const two = (1) + ((1) + (0));
const ten = (1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))));
const twenty = ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))))) * (two);
const test_list = [(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...([twenty, ...([(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...([twenty, ...([])])])])];
const main = ((debug_print)(null))((test_list).map((x) => (x) ** (two)));
(main)()