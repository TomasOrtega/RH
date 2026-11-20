import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H D l Xo P p i S hS s o o₁ o₂ ψ₁ ψ₂ K f₁ f₂ n₁ n₂ hA hK h₁ h₂ i₁ i₂ k₁ k₂`. Take `⟨-, -, hp, hpP, hM⟩` from `hA`. Establish `hnat : ∀ {T : Over S} (x : T ⟶ o.t.G) (n : ℕ), x ≫ o.t.act.act (n : 𝓞 E) = x ^ n`. Introduce `T x n`. Proceed by induction on `n with`.

Consider the case `zero`. Establish `h` using `o.t.act.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h0 : o.t.act.act 0 = 1` using `by simpa using h`. Rewrite using `[Nat.cast_zero, pow_zero, h0, MonObj.comp_one]`.

Consider the case `succ n ih => rw [Nat.cast_succ, o.t.act.add, MonObj.comp_mul, ih, o.t.act.one, Category.comp_id, pow_succ]`. Establish `hkill : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1`. Introduce `k _ _ x z hz`. Take `⟨C, hC, hH⟩` from `hK k x`. Establish `hzC` using `hH.2.2.1 ((hC z).2 hz)`.

Establish `hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E)`. Use `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `h` using `hzC ((p ^ 2 : ℕ) : 𝓞 E) (by`. Rewrite using `[Nat.cast_pow, pow_two]`.

Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)`. Rewrite `h` using `[hnat]`. Then use the resulting hypothesis. Take `⟨m, hm⟩` from `GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o₁ o₂ ψ₁ ψ₂ K hp hM i₁ i₂ k₁ k₂ hkill`. Take `⟨m', hm'⟩` from `((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 f₂ (𝟙 S) n₂).1 m`. Establish `hf : f₁ = 𝟙 S ≫ f₂` using `(Xo.rep S s hS o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp, h₂], ⟨m'⟩⟩`.

Use `⟨by rw [hf, Category.id_comp], ?_⟩` and prove the remaining obligations. Substitute `hf` using the available equality. Establish `e` using `GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o₁ _ (Or.inl hS) n₁.toSABMap m'.toSABMap (fun a => ⟨_, n₁.eta a, m'.eta a⟩)`. Rewrite using `[e, hm', ← Category.assoc, hm]`.
-/
theorem heckeQuot_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  intro E _ _ _ H D l Xo P p i S hS s o o₁ o₂ ψ₁ ψ₂ K f₁ f₂ n₁ n₂ hA hK h₁ h₂ i₁ i₂ k₁ k₂
  obtain ⟨-, -, hp, hpP, hM⟩ := hA
  have hnat : ∀ {T : Over S} (x : T ⟶ o.t.G) (n : ℕ), x ≫ o.t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := o.t.act.add 0 0
      rw [add_zero] at h
      have h0 : o.t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.t.act.add, MonObj.comp_mul, ih, o.t.act.one, Category.comp_id, pow_succ]
  have hkill : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G),
      Set.range z.left ⊆ K → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hH⟩ := hK k x
    have hzC := hH.2.2.1 ((hC z).2 hz)
    have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
      rwa [map_natCast] at this
    have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
      rw [Nat.cast_pow, pow_two]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
    rwa [hnat] at h
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o₁ o₂ ψ₁ ψ₂ K hp hM i₁ i₂ k₁ k₂ hkill
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2
    f₂ (𝟙 S) n₂).1 m
  have hf : f₁ = 𝟙 S ≫ f₂ :=
    (Xo.rep S s hS o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp, h₂], ⟨m'⟩⟩
  refine ⟨by rw [hf, Category.id_comp], ?_⟩
  subst hf
  have e := GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o₁ _ (Or.inl hS)
    n₁.toSABMap m'.toSABMap (fun a => ⟨_, n₁.eta a, m'.eta a⟩)
  rw [e, hm', ← Category.assoc, hm]

end GlobalTheory
