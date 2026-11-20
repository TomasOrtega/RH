import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.CertificateRingHomMap Module

/- English proof (translation)
Set `G : Submodule ℂ M` to `⨅ j, (S j).maxGenEigenspace (θ j)`. Establish `hyG : y ∈ G` using `(Submodule.mem_iInf _).2 hG`. Establish `hGne : G ≠ ⊥` using `fun h => hy (by rw [h] at hyG; simpa using hyG)`. Establish `hst : ∀ j, ∀ x ∈ G, S j x ∈ G`. Introduce `j x hx`.

Use `(Submodule.mem_iInf _).2 fun i => ?_` and prove the remaining obligations. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm (show Commute (S i) (S j) from hS i j) (θ i) ((Submodule.mem_iInf _).1 hx i)`. Take `⟨v, hvG, hv0, hv⟩` from `UpperTheory.V.LinAlg.simEig S hS _ G rfl hGne hst`. Use `⟨v, hv0, fun j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hv j`.

Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hvG j)`. Establish `h1 : (S j - θ j • (1 : End ℂ M)) v = (c - θ j) • v`. Simplify using `[hc, sub_smul]`. Establish `hp : ∀ n : ℕ, ((S j - θ j • (1 : End ℂ M)) ^ n) v = (c - θ j) ^ n • v`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']`. Rewrite `hk` using `[hp]`. Break down `smul_eq_zero.1 hk with h | h` into its components or cases.

Establish `: c = θ j` using `sub_eq_zero.1 (by_contra fun h' => pow_ne_zero k h' h)`. Rewrite using `[hc, this]`. Conclude with `absurd h hv0`.
-/
private lemma common_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (S : J → End ℂ M) (hS : ∀ i j, S i * S j = S j * S i) (θ : J → ℂ) (y : M) (hy : y ≠ 0)
    (hG : ∀ j, y ∈ (S j).maxGenEigenspace (θ j)) : ∃ x : M, x ≠ 0 ∧ ∀ j, S j x = θ j • x := by
  let G : Submodule ℂ M := ⨅ j, (S j).maxGenEigenspace (θ j)
  have hyG : y ∈ G := (Submodule.mem_iInf _).2 hG
  have hGne : G ≠ ⊥ := fun h => hy (by rw [h] at hyG; simpa using hyG)
  have hst : ∀ j, ∀ x ∈ G, S j x ∈ G := by
    intro j x hx
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (show Commute (S i) (S j) from hS i j) (θ i)
      ((Submodule.mem_iInf _).1 hx i)
  obtain ⟨v, hvG, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig S hS _ G rfl hGne hst
  refine ⟨v, hv0, fun j => ?_⟩
  obtain ⟨c, hc⟩ := hv j
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hvG j)
  have h1 : (S j - θ j • (1 : End ℂ M)) v = (c - θ j) • v := by
    simp [hc, sub_smul]
  have hp : ∀ n : ℕ, ((S j - θ j • (1 : End ℂ M)) ^ n) v = (c - θ j) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [hp] at hk
  rcases smul_eq_zero.1 hk with h | h
  · have : c = θ j := sub_eq_zero.1 (by_contra fun h' => pow_ne_zero k h' h)
    rw [hc, this]
  · exact absurd h hv0

/- English proof (translation)
Establish `hw : ∀ (w : List J) (x : U), (((w.map fun j => (T j).restrict (h j)).prod x : U) : M) = (w.map T).prod (x : M)`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro x`. Simplify using the standard rewrite rules.

Consider the case `cons j w ih`. Introduce `x`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.restrict_coe_apply, ih]`. Unfold `wop`. Simplify using `only [Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, hw]`.
-/
private lemma wop_restrict {M J : Type} [AddCommGroup M] [Module ℂ M] (U : Submodule ℂ M)
    (T : J → End ℂ M) (h : ∀ j, ∀ x ∈ U, T j x ∈ U) (s : List J →₀ ℂ) (x : U) :
    ((wop (fun j => (T j).restrict (h j)) s x : U) : M) = wop T s (x : M) := by
  have hw : ∀ (w : List J) (x : U),
      (((w.map fun j => (T j).restrict (h j)).prod x : U) : M) = (w.map T).prod (x : M) := by
    intro w
    induction w with
    | nil => intro x; simp
    | cons j w ih =>
      intro x
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.restrict_coe_apply, ih]
  unfold wop
  simp only [Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul, hw]

end UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Use `open UpperTheory.Gal.CertificateRingHomMap Module in`. Introduce `hP B J _ W _ _ _ T u θ hc`. Set `U : ∀ b, Submodule ℂ (W b)` to `fun b => Submodule.span ℂ {x | ∃ (w : List J) (z : W b), x = ((w.map (T b)).prod * u b) z}`. Establish `hst : ∀ b j, ∀ x ∈ U b, T b j x ∈ U b`. Introduce `b j x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨w, z, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨j :: w, z, by simp [Module.End.mul_apply]⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hcm : ∀ b j j', ∀ x ∈ U b, T b j (T b j' x) = T b j' (T b j x)`.

Introduce `b j j' x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨w, z, rfl⟩` from `h`. Use `LinearMap.congr_fun (hc b j j' w) z` as an intermediate fact.

Simplify `this` using `[Module.End.mul_apply]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Consider the case `smul a x _ hx => simp only [map_smul, hx]`. Set `S : ∀ b, J → End ℂ (U b)` to `fun b j => (T b j).restrict (hst b j)`.

Establish `hS : ∀ b j j', S b j * S b j' = S b j' * S b j`. Introduce `b j j'`. Use extensionality with `⟨x, hx⟩`. Conclude with `hcm b j j' x hx`. Set `T' : J → ∀ b, End ℂ (U b)` to `fun j b => S b j`.

Consider the cases of `nonempty_fintype B`. Take `⟨s, h1, -, h3⟩` from `hP ℂ (∀ b, End ℂ (U b)) J T' (fun i j => funext fun b => hS b i j) θ`. Use `⟨s, h1, fun b hne => ?_⟩` and prove the remaining obligations. Establish `hev : (wop T' s) b = wop (S b) s` using `map_wop (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) T' s`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, (wop (T b) s * u b) z ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (LinearMap.ext h)`. Establish `hu : u b z ∈ U b` using `Submodule.subset_span ⟨[], z, by simp⟩`. Establish `hcoe : ((wop (S b) s ⟨u b z, hu⟩ : U b) : W b) = wop (T b) s (u b z)` using `wop_restrict (U b) (T b) (hst b) s ⟨u b z, hu⟩`.

Establish `hy : wop (S b) s ⟨u b z, hu⟩ ≠ 0`. Introduce `h`. Apply `hz` to reduce the goal to its premises. Rewrite using `[Module.End.mul_apply, ← hcoe, h]`. Both sides reduce to the same expression.

Establish `hyG : ∀ j, wop (S b) s ⟨u b z, hu⟩ ∈ (S b j).maxGenEigenspace (θ j)`. Introduce `j`. Take `⟨N, hN⟩` from `h3 j`. Establish `hN'` using `congrArg (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) hN`. Rewrite `hN'` using `[map_mul, map_pow, map_sub, AlgHom.commutes, map_zero]`.

Use `(Module.End.mem_maxGenEigenspace _ _ _).2 ⟨N, ?_⟩` and prove the remaining obligations. Establish `h2 : (S b j - θ j • (1 : End ℂ (U b))) ^ N * wop (S b) s = 0`. Rewrite `*` using `[← hev, Algebra.algebraMap_eq_smul_one]`. Conclude with `hN'`. Use `LinearMap.congr_fun h2 ⟨u b z, hu⟩` as an intermediate fact.

Simplify `this` using `[Module.End.mul_apply]`. Take `⟨x, hx0, hx⟩` from `common_eig (S b) (hS b) θ _ hy hyG`. Use `⟨(x : W b), fun h => hx0 (Subtype.ext h), fun j => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (hx j)`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.eigOf_of :
    UpperTheory.Gal.CertificateRingHomMap.ProjOne.{0} → EigOf := by
  open UpperTheory.Gal.CertificateRingHomMap Module in
  intro hP B J _ W _ _ _ T u θ hc
  let U : ∀ b, Submodule ℂ (W b) := fun b =>
    Submodule.span ℂ {x | ∃ (w : List J) (z : W b), x = ((w.map (T b)).prod * u b) z}
  have hst : ∀ b j, ∀ x ∈ U b, T b j x ∈ U b := by
    intro b j x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      exact Submodule.subset_span ⟨j :: w, z, by simp [Module.End.mul_apply]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hcm : ∀ b j j', ∀ x ∈ U b, T b j (T b j' x) = T b j' (T b j x) := by
    intro b j j' x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      have := LinearMap.congr_fun (hc b j j' w) z
      simpa [Module.End.mul_apply] using this
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx => simp only [map_smul, hx]
  let S : ∀ b, J → End ℂ (U b) := fun b j => (T b j).restrict (hst b j)
  have hS : ∀ b j j', S b j * S b j' = S b j' * S b j := by
    intro b j j'
    ext ⟨x, hx⟩
    exact hcm b j j' x hx
  let T' : J → ∀ b, End ℂ (U b) := fun j b => S b j
  cases nonempty_fintype B
  obtain ⟨s, h1, -, h3⟩ := hP ℂ (∀ b, End ℂ (U b)) J T' (fun i j => funext fun b => hS b i j) θ
  refine ⟨s, h1, fun b hne => ?_⟩
  have hev : (wop T' s) b = wop (S b) s := map_wop (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) T' s
  obtain ⟨z, hz⟩ : ∃ z, (wop (T b) s * u b) z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (LinearMap.ext h)
  have hu : u b z ∈ U b := Submodule.subset_span ⟨[], z, by simp⟩
  have hcoe : ((wop (S b) s ⟨u b z, hu⟩ : U b) : W b) = wop (T b) s (u b z) :=
    wop_restrict (U b) (T b) (hst b) s ⟨u b z, hu⟩
  have hy : wop (S b) s ⟨u b z, hu⟩ ≠ 0 := by
    intro h
    apply hz
    rw [Module.End.mul_apply, ← hcoe, h]
    rfl
  have hyG : ∀ j, wop (S b) s ⟨u b z, hu⟩ ∈ (S b j).maxGenEigenspace (θ j) := by
    intro j
    obtain ⟨N, hN⟩ := h3 j
    have hN' := congrArg (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) hN
    rw [map_mul, map_pow, map_sub, AlgHom.commutes, map_zero] at hN'
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨N, ?_⟩
    have h2 : (S b j - θ j • (1 : End ℂ (U b))) ^ N * wop (S b) s = 0 := by
      rw [← hev, Algebra.algebraMap_eq_smul_one] at *
      exact hN'
    have := LinearMap.congr_fun h2 ⟨u b z, hu⟩
    simpa [Module.End.mul_apply] using this
  obtain ⟨x, hx0, hx⟩ := common_eig (S b) (hS b) θ _ hy hyG
  refine ⟨(x : W b), fun h => hx0 (Subtype.ext h), fun j => ?_⟩
  exact congrArg Subtype.val (hx j)
