# Irrationality of Li₂(½)

A Lean 4 proof that

$$\mathrm{Li}_2(1/2) = \sum_{n = 1}^\infty \frac{1}{2^n n^2}$$

is irrational.

The main theorem is `li2_one_half_irrational` in [`Li2Half.lean`](Li2Half.lean):

```lean
theorem li2_one_half_irrational :
    Irrational (∑' k : ℕ, (1/2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2)
```

`Irrational` is defined in Mathlib's [`Mathlib/NumberTheory/Real/Irrational.lean`](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/NumberTheory/Real/Irrational.lean#L35-L38):

```lean
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)
```

Thus `Irrational x` means that `x` is not the image of any rational number under the usual inclusion into the reals.

Here `ℕ`, `ℚ`, and `ℝ` denote the natural, rational, and real numbers. The notation `∑'` is Mathlib's [`tsum`](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L131-L160), the infinite sum (defined as zero when the family is not summable). The cast `(k : ℝ)` views the natural number `k` as a real number, and `k + 1` starts the series at 1. Both source links use the Mathlib revision pinned by this project.

## Checking the proof

The project uses Lean `v4.35.0-rc3` and a pinned Mathlib revision (see `lake-manifest.json`).

```sh
lake exe cache get
lake build
```

On machines with limited memory, use `LEAN_NUM_THREADS=4 lake build` to limit the number of concurrent module builds.

The build ends by printing the axioms used by the main theorem:

```
'li2_one_half_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof has also been checked with [comparator](https://github.com/leanprover/comparator), against a statement that uses only Mathlib, and with the independent [nanoda](https://github.com/ammkrn/nanoda_lib) kernel.

## Discussion

https://chaoli.club/index.php/12296

## Acknowledgements

I thank [Siqi Liu](https://github.com/siqiliu-tsinghua) for suggesting the problem and for helpful discussions. I also thank FatFish for support and discussions.

## Credits and license

Some files are adapted from other Apache-2.0 Lean projects; see [`NOTICE`](NOTICE) for the sources and authors. This project is released under the Apache License 2.0 ([`LICENSE`](LICENSE)).
