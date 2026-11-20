import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShDesc

universe w

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

def cechMap (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S) (n : ℕ) : P.cech.X n →ₗ[R] Q.cech.X n :=
  LinearMap.pi fun i => (e (ent i)).comp (LinearMap.proj i)

/- English proof (translation)
Rewrite using `[Cos.d_apply, Cos.d_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Conclude with `(hn _ _).symm`.
-/
theorem cechMap_d (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (cechMap P Q e n x) = cechMap P Q e (n + 1) (P.cech.d n x) := by
  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (hn _ _).symm

/- English proof (translation)
Use function extensionality and compare the values at `t`. Conclude with `(hn _ _).symm`.
-/
theorem cechMap_aug (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (x : P.M ∅) :
    Q.aug (e ∅ x) = cechMap P Q e 0 (P.aug x) := by
  funext t
  exact (hn _ _).symm

/- English proof (translation)
Establish `hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x)`. Introduce `S T h x`. Apply `(e T).injective` to reduce the goal to its premises. Rewrite using `[hn]`. Simplify using the standard rewrite rules.

Set `f : ∀ S, P.M S →ₗ[R] Q.M S` to `fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)`. Set `g : ∀ S, Q.M S →ₗ[R] P.M S` to `fun S => ((e S) : Q.M S →ₗ[R] P.M S)`. Establish `hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x)` using `hn'`. Establish `hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x)` using `hn`. Establish `fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y`.

Introduce `n y`. Use function extensionality and compare the values at `t`. Conclude with `(e _).symm_apply_apply _`. Establish `gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y`. Introduce `n y`.

Use function extensionality and compare the values at `t`. Conclude with `(e _).apply_symm_apply _`. Take `⟨h0, h1, h2, h3⟩` from `hP`. Use `⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩` and prove the remaining obligations. Establish `: Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y))`.

Rewrite using `[← cechMap_aug P Q f hf]`. Use `congr 1`. Conclude with `((e ∅).symm_apply_apply y).symm`. Express the relevant statement in the definitionally equal form `Q.cech.d 0 (Q.aug y) = 0`. Rewrite using `[this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]`.

Establish `h` using `h1 (g ∅ y) (by`. Use `cechMap_aug Q P g hg y` as an intermediate fact. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `cechMap Q P g 0 (Q.aug y) = 0 at *`. Rewrite using `[hy, map_zero])`.

Rewrite `h`, the goal using `[one_smul]`. Conclude with `(e ∅).injective (by rw [map_zero]; exact h)`. Take `⟨x, hx⟩` from `h2 (cechMap Q P g 0 y) (by`. Express the relevant statement in the definitionally equal form `P.cech.d 0 _ = 0`. Rewrite using `[cechMap_d Q P g hg]`.

Establish `hy' : Q.cech.d 0 y = 0` using `hy`. Rewrite using `[hy', map_zero])`. Use `⟨f ∅ x, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[one_smul]`. Rewrite using `[cechMap_aug P Q f hf]`.

Establish `hx' : P.aug x = cechMap Q P g 0 y` using `hx`. Rewrite using `[hx', fg]`. Take `⟨x, hx⟩` from `h3 n (cechMap Q P g (n + 1) y) (by`. Express the relevant statement in the definitionally equal form `P.cech.d (n + 1) _ = 0`. Rewrite using `[cechMap_d Q P g hg]`.

Establish `hy' : Q.cech.d (n + 1) y = 0` using `hy`. Rewrite using `[hy', map_zero])`. Use `⟨cechMap P Q f n x, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[one_smul]`. Express the relevant statement in the definitionally equal form `Q.cech.d n _ = y`.

Rewrite using `[cechMap_d P Q f hf]`. Establish `hx' : P.cech.d n x = cechMap Q P g (n + 1) y` using `hx`. Rewrite using `[hx', fg]`.
-/
theorem ex_of_equiv (P Q : PM.{w} R ι) (e : ∀ S, Q.M S ≃ₗ[R] P.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (Q.res h x) = P.res h (e S x)) (hP : P.Ex) : Q.Ex := by
  have hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x) := by
    intro S T h x
    apply (e T).injective
    rw [hn]
    simp
  let f : ∀ S, P.M S →ₗ[R] Q.M S := fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)
  let g : ∀ S, Q.M S →ₗ[R] P.M S := fun S => ((e S) : Q.M S →ₗ[R] P.M S)
  have hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x) := hn'
  have hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x) := hn
  have fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y := by
    intro n y
    funext t
    exact (e _).symm_apply_apply _
  have gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y := by
    intro n y
    funext t
    exact (e _).apply_symm_apply _
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · have : Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y)) := by
      rw [← cechMap_aug P Q f hf]
      congr 1
      exact ((e ∅).symm_apply_apply y).symm
    change Q.cech.d 0 (Q.aug y) = 0
    rw [this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]
  · have h := h1 (g ∅ y) (by
      have := cechMap_aug Q P g hg y
      rw [this]
      change cechMap Q P g 0 (Q.aug y) = 0 at *
      rw [hy, map_zero])
    rw [one_smul] at h ⊢
    exact (e ∅).injective (by rw [map_zero]; exact h)
  · obtain ⟨x, hx⟩ := h2 (cechMap Q P g 0 y) (by
      change P.cech.d 0 _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d 0 y = 0 := hy
      rw [hy', map_zero])
    refine ⟨f ∅ x, ?_⟩
    rw [one_smul] at hx ⊢
    rw [cechMap_aug P Q f hf]
    have hx' : P.aug x = cechMap Q P g 0 y := hx
    rw [hx', fg]
  · obtain ⟨x, hx⟩ := h3 n (cechMap Q P g (n + 1) y) (by
      change P.cech.d (n + 1) _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d (n + 1) y = 0 := hy
      rw [hy', map_zero])
    refine ⟨cechMap P Q f n x, ?_⟩
    rw [one_smul] at hx ⊢
    change Q.cech.d n _ = y
    rw [cechMap_d P Q f hf]
    have hx' : P.cech.d n x = cechMap Q P g (n + 1) y := hx
    rw [hx', fg]

/- English proof (translation)
Establish `hX : ∀ n, Subsingleton (P.cech.X n)` using `fun n => inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))`. Use `⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _, fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩` and prove the remaining obligations.
-/
theorem ex_of_subsingleton (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have hX : ∀ n, Subsingleton (P.cech.X n) := fun n =>
    inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))
  refine ⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _,
    fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩

variable {K : Type} [Field K]

def shEv (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m :=
  LinearEquiv.ofBijective
    (LinearMap.proj (φ := fun p : {p : ℕ // p + k = n} => C.X p.1) ⟨m, h⟩) (by
    constructor
    · intro y y' hyy
      funext ⟨p, hp⟩
      obtain rfl : p = m := by omega
      exact hyy
    · intro x
      refine ⟨fun p => (show m = p.1 by have := p.2; omega) ▸ x, rfl⟩)

/- English proof (translation)
Introduce `n`. Distinguish the cases in `hk : k ≤ n`. Establish `h : n - k + k = n` using `by omega`. Conclude with `ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h) (fun _ _ => rfl) (hA (n - k))`. Use `ex_of_subsingleton _ fun S => ?_` and prove the remaining obligations.

Establish `: IsEmpty {m : ℕ // m + k = n}` using `⟨fun p => hk (by have := p.2; omega)⟩`. Conclude with `inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))`.
-/
theorem shSy_desc {ς : ℤˣ} {k : ℕ} {A : Sy.{w} K ι} (hA : A.Desc) : (shSy ς k A).Desc := by
  intro n
  by_cases hk : k ≤ n
  · have h : n - k + k = n := by omega
    exact ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h)
      (fun _ _ => rfl) (hA (n - k))
  · refine ex_of_subsingleton _ fun S => ?_
    have : IsEmpty {m : ℕ // m + k = n} := ⟨fun p => hk (by have := p.2; omega)⟩
    exact inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))

/- English proof (translation)
Introduce `_ _ _ h` and use `shSy_desc h`.
-/
theorem sh_desc : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι),
    A.Desc → (shSy ς k A).Desc :=
  fun _ _ _ h => shSy_desc h

end GlobalTheory.CompanionTheory.KunGlue.ShDesc
