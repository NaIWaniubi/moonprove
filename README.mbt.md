# moonprove

把断言变成证明，或者给出反例。一个针对 MoonBit 风格代码的有界验证器。

```
$ moonprove verify examples/06_loop.mbt
domain: Int parameters lie in [-1073741824, 1073741823]
line 4  invariant on entry  proven
line 4  invariant preserved  proven
line 7  assert  proven
3 obligation(s): 3 proven, 0 violated, 0 undecided
```

每条 `assert` / `require` / `ensure` / `invariant` 得到三种判决之一：**证明成立**、**被反例推翻**、**证不出来**。没有第四种，中间那块空白如实报告。

支撑它的是一个真的判定过程：化简 + 区间反驳 + Fourier–Motzkin 消元 + 边界搜索。`Unsat`（证明）只来自前三者，`Sat`（反例）只来自校验过的模型，其余是 `Unknown`。

循环用归纳而不是展开，所以无限循环也能验证；没有 `invariant` 的循环会明说无法证明。

浏览器里的 playground 和 CLI 是同一份代码编译到 wasm。

完整说明见 [README.md](README.md)，设计与边界见 [docs/DESIGN.md](docs/DESIGN.md)。
