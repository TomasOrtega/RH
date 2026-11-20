import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Introduce `x _` and use `by simp [locChar]`.
-/
theorem unrAt_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 E)) : UnrAt (1 : Chr F E) w := fun x _ => by
  simp [locChar]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hX v w hw hv z hz`. Establish `h : w.under (𝓞 F) = v` using `(GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl`. Establish `hwT : w ∉ above E (X.T : Set (Pl F))` using `fun hm => hv (h ▸ hm)`. Establish `hev : Even (a' + a)` using `by rw [add_comm]; exact hX.geo.even`. Establish `hres : ∀ b : (AF F)ˣ, (X.α * X.β) (ideleMap F E b) = (1 : Chr F E) (ideleMap F E b)`.

Introduce `b`. Establish `hA : ((X.α (ideleMap F E b) : Circle) : ℂ) = _` using `hX.chars.resα b`. Establish `hB : ((X.β (ideleMap F E b) : Circle) : ℂ) = _` using `hX.chars.resβ b`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.one_apply, ← Circle.coe_eq_one, Circle.coe_mul, hA, hB]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[← pow_add, hev.neg_one_pow]`. Establish `key` using `GlobalTheory.InertChars.locIdele_eq_of_inert hw (X.α * X.β) 1 hres ((hX.chars.unrα w hwT).mul (hX.chars.unrβ w hwT)) (unrAt_one w)`. Use `⟨?_, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hX v w hw hv z hz⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.InertChars.eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw, ← MonoidHom.mul_apply, key, MonoidHom.one_apply]`.
-/
theorem charSt : CharSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hX v w hw hv z hz
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have hwT : w ∉ above E (X.T : Set (Pl F)) := fun hm => hv (h ▸ hm)
  have hev : Even (a' + a) := by rw [add_comm]; exact hX.geo.even
  have hres : ∀ b : (AF F)ˣ, (X.α * X.β) (ideleMap F E b) = (1 : Chr F E) (ideleMap F E b) := by
    intro b
    have hA : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resα b
    have hB : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resβ b
    rw [MonoidHom.mul_apply, MonoidHom.one_apply, ← Circle.coe_eq_one, Circle.coe_mul, hA, hB]
    split_ifs
    · simp
    · rw [← pow_add, hev.neg_one_pow]
  have key := GlobalTheory.InertChars.locIdele_eq_of_inert hw (X.α * X.β) 1 hres
    ((hX.chars.unrα w hwT).mul (hX.chars.unrβ w hwT)) (unrAt_one w)
  refine ⟨?_, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hX v w hw hv z hz⟩
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw, ← MonoidHom.mul_apply, key,
    MonoidHom.one_apply]

end PositivityTheory.Sph

end
