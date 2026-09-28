# Irrationality of Li₂(1/2)

A Lean 4 proof that

$$\mathrm{Li}_2(1/2) = \sum_{n \ge 1} \frac{1}{2^n n^2}$$

is irrational.

The main theorem is `li2_one_half_irrational` in [`Li2Half.lean`](Li2Half.lean):

```lean
theorem li2_one_half_irrational :
    Irrational (∑' k : ℕ, (1/2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2)
```

## Checking the proof

The project uses Lean `v4.30.0-rc2` and a pinned Mathlib revision (see `lake-manifest.json`).

```sh
lake exe cache get
lake build
```

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
