import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor

noncomputable section

namespace GlobalTheory.LoopC.Centre

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def nil (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ a, ∑ a', (c a a' • S.hT (e a')).smulRight (e a)

/- English proof (translation)
Simplify using `[nil]`.
-/
theorem nil_apply (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V) :
    nil e c x = ∑ a, ∑ a', (c a a' * S.hT (e a') x) • e a := by
  simp [nil]

/- English proof (translation)
Rewrite using `[nil_apply]`. Simplify using `[hx]`.
-/
theorem nil_eq_zero (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V)
    (hx : ∀ a, S.hT (e a) x = 0) : nil e c x = 0 := by
  rw [nil_apply]
  simp [hx]

/- English proof (translation)
Rewrite using `[nil_apply, map_sum]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, he, smul_zero]`.
-/
theorem hT_nil (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) (a : Fin r) : S.hT (e a) (nil e c x) = 0 := by
  rw [nil_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [LinearMap.map_smul, he, smul_zero]

def cen (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (LinearMap.id + nil e c) (LinearMap.id - nil e c)
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cen_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) : cen e he c x = x + nil e c x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cen_symm_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0)
    (c : Matrix (Fin r) (Fin r) E) (x : S.V) : (cen e he c).symm x = x - nil e c x := rfl

/- English proof (translation)
Establish `hstar : ∀ a a', starRingEnd E (c a a') = -c a' a`. Introduce `a a'`. Establish `h` using `congrFun (congrFun hc a') a`. Rewrite using `[starRingEnd_apply]`. Simplify `h` using `[Matrix.conjTranspose_apply]`.

Establish `hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u` using `S.herm.eq`. Establish `hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0`. Introduce `x y`. Rewrite using `[nil_apply e c x, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]`. Establish `hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0`. Introduce `x y`.

Simplify using `only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun a' _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y`. Introduce `x y`. Rewrite using `[cen_apply, cen_apply]`. Simplify using `only [map_add, LinearMap.add_apply]`.

Rewrite using `[hnn, add_zero]`. Take the linear combination `hcross x y`.
-/
theorem cen_isom (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (hc : cᴴ = -c) : cen e he c ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hstar : ∀ a a', starRingEnd E (c a a') = -c a' a := by
    intro a a'
    have h := congrFun (congrFun hc a') a
    rw [starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using h
  have hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u := S.herm.eq

  have hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0 := by
    intro x y
    rw [nil_apply e c x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]

  have hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0 := by
    intro x y
    simp only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    ring
  show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y
  intro x y
  rw [cen_apply, cen_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [hnn, add_zero]
  linear_combination hcross x y

/- English proof (translation)
Rewrite using `[nil_apply]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_` and prove the remaining obligations. Establish `hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ`. Establish `h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ` using `hΛ`. Rewrite using `[h']`.

Conclude with `hx`. Establish `h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E)`. Establish `h2` using `(Submodule.mem_iInf _).mp hd (e a')`. Establish `h3` using `(Submodule.mem_iInf _).mp h2 (heΛ a')`. Conclude with `h3`.

Take `⟨o, ho⟩` from `Submodule.mem_one.mp h1`. Rewrite using `[Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]`. Conclude with `Λ.smul_mem _ (heΛ a)`.
-/
theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (e : Fin r → S.V)
    (heΛ : ∀ a, e a ∈ Λ) (c : Matrix (Fin r) (Fin r) (𝓞 E)) (x : S.V) (hx : x ∈ Λ) :
    nil e (c.map (algebraMap (𝓞 E) E)) x ∈ Λ := by
  rw [nil_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_
  have hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h']
    exact hx
  have h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E) := by
    have h2 := (Submodule.mem_iInf _).mp hd (e a')
    have h3 := (Submodule.mem_iInf _).mp h2 (heΛ a')
    exact h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  rw [Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]
  exact Λ.smul_mem _ (heΛ a)

/- English proof (translation)
Establish `hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0` using `F.fl.e_iso`. Establish `hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0`. Introduce `a' x hx`. Establish `hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a'))` using `by show Submodule.span E (Set.range F.fl.e) ≤ _`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `LinearMap.mem_ker.mpr (hiso a' b)`. Conclude with `LinearMap.mem_ker.mp (hle hx)`. Establish `hXe : ∀ a, F.fl.e a ∈ Xsp F`. Introduce `a`.

Use `show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Establish `hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x`. Introduce `x hx`. Rewrite using `[cen_apply, nil_eq_zero _ _ _ ?_, add_zero]`.

Introduce `a'`. Establish `h2` using `(Submodule.mem_iInf _).mp hx (F.fl.e a')`. Conclude with `LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))`. Establish `hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b`. Introduce `b`.

Rewrite using `[cen_apply, nil_eq_zero _ _ _ ?_, add_zero]`. Introduce `a'`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'`. Consider the case `cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i`.

Establish `hflag : ∀ j, ∀ x ∈ Xflag F (j + 1), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j`. Introduce `j x hx`. Establish `hle : Xflag F (j + 1) ≤ Xsp F` using `by show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)`. Conclude with `Submodule.span_mono (Set.image_subset_range _ _)`. Rewrite using `[cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]`.

Conclude with `zero_mem _`. Establish `horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F`. Introduce `x hx`. Rewrite using `[hfix x hx, sub_self]`. Conclude with `zero_mem _`.

Establish `hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ` using `by show Submodule.map _ Λ = Λ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Use `show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ`.

Rewrite using `[cen_apply]`. Conclude with `Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)`. Introduce `y hy`. Use `Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y, Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩` and prove the remaining obligations. Use `show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y`.

Rewrite using `[← cen_symm_apply F.fl.e hiso _ y]`. Conclude with `LinearEquiv.apply_symm_apply _ y`. Establish `hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F`. Simplify using `only [NLam, IsAutLam, Set.mem_setOf_eq]`. Conclude with `⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩`.

Use `⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[cen_apply, nil_apply]`. Both sides reduce to the same expression.
-/
theorem centre_gen {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (heΛ : ∀ a, F.fl.e a ∈ Λ)
    (c : Matrix (Fin r) (Fin r) (𝓞 E))
    (hc : (c.map (algebraMap (𝓞 E) E))ᴴ = -c.map (algebraMap (𝓞 E) E)) :
    ∃ n : S.V ≃ₗ[E] S.V, (n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b) ∧
      (∀ x ∈ orth S (Xsp F), n x = x) ∧
      ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : E) * S.hT (F.fl.e a') x) • F.fl.e a := by
  have hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0 := F.fl.e_iso

  have hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0 := by
    intro a' x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a')) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (hiso a' b)
    exact LinearMap.mem_ker.mp (hle hx)
  have hXe : ∀ a, F.fl.e a ∈ Xsp F := by
    intro a
    show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨a, rfl⟩

  have hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x := by
    intro x hx
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    have h2 := (Submodule.mem_iInf _).mp hx (F.fl.e a')
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))

  have hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b := by
    intro b
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    induction b using Fin.lastCases with
    | last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'
    | cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i

  have hflag : ∀ j, ∀ x ∈ Xflag F (j + 1),
      cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j := by
    intro j x hx
    have hle : Xflag F (j + 1) ≤ Xsp F := by
      show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)
      exact Submodule.span_mono (Set.image_subset_range _ _)
    rw [cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]
    exact zero_mem _
  have horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F := by
    intro x hx
    rw [hfix x hx, sub_self]
    exact zero_mem _

  have hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ := by
    show Submodule.map _ Λ = Λ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ
      rw [cen_apply]
      exact Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y,
        Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y
      rw [← cen_symm_apply F.fl.e hiso _ y]
      exact LinearEquiv.apply_symm_apply _ y
  have hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    exact ⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩
  refine ⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩
  rw [cen_apply, nil_apply]
  rfl

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D T F Λ hΛ heΛ c hc`. Take `⟨n, h1, hfix, hform⟩` from `centre_gen F Λ hΛ heΛ c hc`. Conclude with `⟨n, h1, hfix, hform⟩`.
-/
theorem centralMap_mem_integralUnipotentFixingFrame : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → (∀ a, F.fl.e a ∈ Λ) → ∀ c : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E), (c.map (algebraMap (𝓞 D.host.E) D.host.E))ᴴ = -c.map (algebraMap (𝓞 D.host.E) D.host.E) → ∃ n ∈ N1 D Λ F, (∀ x ∈ orth (hS D) (Xsp F), n x = x) ∧ ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : D.host.E) * (hS D).hT (F.fl.e a') x) • F.fl.e a := by
  intro D T F Λ hΛ heΛ c hc
  obtain ⟨n, h1, hfix, hform⟩ := centre_gen F Λ hΛ heΛ c hc
  exact ⟨n, h1, hfix, hform⟩

end GlobalTheory.LoopC.Centre

end
