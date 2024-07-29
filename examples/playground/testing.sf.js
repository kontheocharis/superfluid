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
const subst = (e) => (n) => (t) => (() => {
  switch ((e)[0]) {
    case "var": return ((n) === ((e)[(1) + (0)])) ? (t) : (["var", (e)[(1) + (0)]]);
    case "app": return ["app", (((subst)((e)[(1) + (0)]))(n))(t), (((subst)((e)[(1) + ((1) + (0))]))(n))(t)];
    case "lam": return ["lam", (((subst)((e)[(1) + (0)]))((1) + (n)))(t)];
  }
})();
const evaluate = (e) => (() => {
  switch ((e)[0]) {
    case "var": return ["var", (e)[(1) + (0)]];
    case "app": return (() => {
      const e1_p_ = (evaluate)((e)[(1) + (0)]);
      return (() => {
        switch ((e1_p_)[0]) {
          case "lam": return (evaluate)((((subst)((e1_p_)[(1) + (0)]))(0))((e)[(1) + ((1) + (0))]));
          case "app": return ["app", ["app", (e1_p_)[(1) + (0)], (e1_p_)[(1) + ((1) + (0))]], (evaluate)((e)[(1) + ((1) + (0))])];
          case "var": return ["app", ["var", (e1_p_)[(1) + (0)]], (evaluate)((e)[(1) + ((1) + (0))])];
        }
      })();
    })();
    case "lam": return ["lam", (evaluate)((e)[(1) + (0)])];
  }
})();
const evaluate_nbe = (ctx) => (e) => (() => {
  switch ((e)[0]) {
    case "var": return (() => {
      const idx = (((e)[(1) + (0)]) < ((ctx).length)) ? ((ctx)[(e)[(1) + (0)]]) : (null);
      return ((idx) === (null)) ? (["vvar", (e)[(1) + (0)]]) : (idx);
    })();
    case "app": return (() => {
      const e1_p_ = ((evaluate_nbe)(ctx))((e)[(1) + (0)]);
      return (() => {
        switch ((e1_p_)[0]) {
          case "vlam": return ((evaluate_nbe)([((evaluate_nbe)((e1_p_)[(1) + (0)]))((e)[(1) + ((1) + (0))]), ...((e1_p_)[(1) + (0)])]))((e1_p_)[(1) + ((1) + (0))]);
          case "vapp": return ["vapp", ["vapp", (e1_p_)[(1) + (0)], (e1_p_)[(1) + ((1) + (0))]], ((evaluate_nbe)(ctx))((e)[(1) + ((1) + (0))])];
          case "vvar": return ["vapp", ["vvar", (e1_p_)[(1) + (0)]], ((evaluate_nbe)(ctx))((e)[(1) + ((1) + (0))])];
        }
      })();
    })();
    case "lam": return ["vlam", ctx, (e)[(1) + (0)]];
  }
})();
const reify = (v) => (() => {
  switch ((v)[0]) {
    case "vlam": return ["lam", (v)[(1) + ((1) + (0))]];
    case "vapp": return ["app", (reify)((v)[(1) + (0)]), (reify)((v)[(1) + ((1) + (0))])];
    case "vvar": return ["var", (v)[(1) + (0)]];
  }
})();
const identity = ["lam", ["var", 0]];
const two = (1) + ((1) + (0));
const ten = (1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))));
const twenty = ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))))) * (two);
const test_list = [(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...([twenty, ...([(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...([twenty, ...([])])])])];
const main = (() => {
  const lam_term = ["app", ["app", ["app", ["lam", ["app", ["var", 0], ["lam", ["lam", ["var", (1) + (0)]]]]], ["lam", ["var", (1) + (0)]]], ["var", 0]], ["var", (1) + ((1) + (0))]];
  const evaluate_alt = (t) => (reify)(((evaluate_nbe)([]))(t));
  return (() => (((_) => ((debug_print)(null))((evaluate_alt)(lam_term)))((((debug_print)(null))((evaluate)(lam_term)))()))());
})();
(main)()