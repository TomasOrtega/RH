import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

/- English proof (translation)
Introduce `hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A`. Establish `hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'` using `RingHom.ext hf₀`. Take `⟨J', hg, hJ₀⟩` from `exists_gauge f A.D₀.P.isLB A.ν.good`. Take `⟨N', ν', e₁, hth⟩` from `GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen`. Establish `hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ` using `e₁ ▸ hJ₀`.

Establish `G` using `(hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2`. Establish `G'` using `(hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2`. Set `I` to `numHom f hf A.ν ν' hJ hth`. Establish `hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z → WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z)` using `fun k hk p p' z h => by`. Take `⟨q, hq, -⟩` from `(G k).1 p`.

Take `⟨q', hq', -⟩` from `(G k).1 p'`. Take `⟨r, hr, -⟩` from `(G' k).1 (qkExt A.bimult f hf p)`. Take `⟨r', hr', -⟩` from `(G' k).1 (qkExt A.bimult f hf p')`. Establish `a` using `numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr`. Establish `a'` using `numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'`.

Rewrite using `[hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr', (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2, (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]`. Both sides reduce to the same expression. Use `choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists`. Use `⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp det := fun σ => ?_ I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance }, rfl, I, rfl, fun _ _ => …` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `DetExtend.exists_factor f σ`.

Take `⟨n, h₁, h₂⟩` from `A.det τ`. Use `A.D₀.P.isAb.smooth` as an intermediate fact. Use `⟨n, ?_, h₂.trans (by` and prove the remaining obligations. Distinguish the cases in `h : τ H.rt = A.ρ`. Rewrite using `[if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]`.

Rewrite using `[if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩`. Establish `e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) = spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))`. Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]`. Rewrite using `[e]`. Conclude with `(DetExtend.lieMult_extend f _ _ τ n).2 h₁`.

Use `ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_) show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))` and prove the remaining obligations. Rewrite using `[AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]`. Establish `h` using `numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)`. Conclude with `⟨q' n a, h.1, h.2, (N'.qEq_equivalence n).refl _⟩`.
-/
theorem exists_arcF_over : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), (∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ A : ArcF D R F, ∃ A' : ArcF D R F', A'.D₀ = A.D₀ ∧ A.Over f A' := by
  intro hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A
  have hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf₀
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f A.D₀.P.isLB A.ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2
  let I := numHom f hf A.ν ν' hJ hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z →
      WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt A.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt A.bimult f hf p')
    have a := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr
    have a' := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'
    rw [hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
      (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists
  refine ⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance },
    rfl, I, rfl, fun _ _ => rfl, fun a y => ?_, fun n a _ => ?_⟩
  · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
    obtain ⟨n, h₁, h₂⟩ := A.det τ
    have := A.D₀.P.isAb.smooth
    refine ⟨n, ?_, h₂.trans (by
      by_cases h : τ H.rt = A.ρ
      · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
      · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
    have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
        spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
      rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]
    rw [e]
    exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁
  · refine ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_)
    show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]
  · have h := numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)
    exact ⟨q' n a, h.1, h.2, (N'.qEq_equivalence n).refl _⟩

end GlobalTheory.ArcExt
end
