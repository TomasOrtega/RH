import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianFormCount

/- English proof (translation)
Establish `hC : ∀ v : cone p (lbPow L N) s, ∃ (x : Sp K ⟶ X) (l : PUnit → L.ι) (c : K) (_ : x ≫ p = 𝟙 _) (h : ⊤ ≤ x ⁻¹ᵁ SectionRing.chart L l), ∀ j, v.1 j = TorsionZero.val x _ h ((s j).f l) * c`. Introduce and unpack `⟨v, x, hx, l, c, hl, hv⟩`. Conclude with `⟨x, l, c, hx, hl, fun j => (hv j).trans ((_root_.mul_comm _ _).trans (congrArg (· * (c : K)) (dif_pos hl)))⟩`. Use `choose x l c hx hl hv using hC`. Set `β : Fin m → cone p (lbPow L N) s → K` to `fun i v => TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) * c v ^ d`.

Establish `le : (MvPolynomial.homogeneousSubmodule J K d).map (LinearMap.pi fun v : cone p (lbPow L N) s => (MvPolynomial.aeval (R` using `K) v.1).toLinearMap) ≤ Submodule.span K (Set.range β) := by`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Establish `hm` using `TorsionZero.aeval_mem_of_isHomogeneous (SectionRing.secs p L) (x := fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) (fun j => (SectionRing.secEquiv p L N (s j)).2) hF`. Take `⟨a, ha⟩` from `hb ((SectionRing.secEquiv p L (N * d)).symm ⟨_, hm⟩)`. Use `(Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, funext fun v => ?_⟩` and prove the remaining obligations.

Set `ev : SectionRing.Fam p L →ₐ[K] K` to `{ (TorsionZero.val (x v) _ (hl v)).comp (SectionRing.evalFam p L (l v)) with commutes' := fun r => TorsionZero.val_const p (x v) (hx v) _ (hl v) r }`. Establish `h1 : ev (MvPolynomial.aeval (fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) F) = ∑ i, a i * TorsionZero.val (x v) _ (hl v) ((b i).f (l v))` using `(congrArg (TorsionZero.val (x v) _ (hl v)) (ha (l v))).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans (congrArg (· * _) (TorsionZero.val_const p (x v) (hx v) _ (hl v) (a i)))))`. Rewrite `h1` using `[MvPolynomial.comp_aeval_apply]`. Express the relevant statement in the definitionally equal form `_ = MvPolynomial.aeval v.1 F`. Rewrite using `[show v.1 = _ from funext (hv v), TorsionZero.aeval_mul_of_isHomogeneous _ _ hF]`.

Use `Eq.trans ?_ (congrArg (· * c v ^ d) h1).symm` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm`. Use `Module.Finite.span_of_finite K (Set.finite_range β)` as an intermediate fact. Conclude with `(Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)`.
-/
theorem hilb_cone_le_of_span {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X) (N d m : ℕ)
    {J : Type} [Finite J] (s : J → (lbPow L N).Sec) (b : Fin m → (lbPow L (N * d)).Sec)
    (hb : ∀ t : (lbPow L (N * d)).Sec, ∃ a : Fin m → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (b i).f j) :
    hilb (cone p (lbPow L N) s) d ≤ m := by
  have hC : ∀ v : cone p (lbPow L N) s, ∃ (x : Sp K ⟶ X) (l : PUnit → L.ι) (c : K) (_ : x ≫ p = 𝟙 _)
      (h : ⊤ ≤ x ⁻¹ᵁ SectionRing.chart L l),
      ∀ j, v.1 j = TorsionZero.val x _ h ((s j).f l) * c := by
    rintro ⟨v, x, hx, l, c, hl, hv⟩
    exact ⟨x, l, c, hx, hl, fun j => (hv j).trans ((_root_.mul_comm _ _).trans
      (congrArg (· * (c : K)) (dif_pos hl)))⟩
  choose x l c hx hl hv using hC
  let β : Fin m → cone p (lbPow L N) s → K := fun i v =>
    TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) * c v ^ d
  have le : (MvPolynomial.homogeneousSubmodule J K d).map
      (LinearMap.pi fun v : cone p (lbPow L N) s => (MvPolynomial.aeval (R := K) v.1).toLinearMap) ≤
      Submodule.span K (Set.range β) := by
    rintro _ ⟨F, hF, rfl⟩
    have hm := TorsionZero.aeval_mem_of_isHomogeneous (SectionRing.secs p L)
      (x := fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L))
      (fun j => (SectionRing.secEquiv p L N (s j)).2) hF
    obtain ⟨a, ha⟩ := hb ((SectionRing.secEquiv p L (N * d)).symm ⟨_, hm⟩)
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, funext fun v => ?_⟩
    let ev : SectionRing.Fam p L →ₐ[K] K :=
      { (TorsionZero.val (x v) _ (hl v)).comp (SectionRing.evalFam p L (l v)) with
        commutes' := fun r => TorsionZero.val_const p (x v) (hx v) _ (hl v) r }
    have h1 : ev (MvPolynomial.aeval (fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) F) =
        ∑ i, a i * TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) :=
      (congrArg (TorsionZero.val (x v) _ (hl v)) (ha (l v))).trans ((map_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans
          (congrArg (· * _) (TorsionZero.val_const p (x v) (hx v) _ (hl v) (a i)))))
    rw [MvPolynomial.comp_aeval_apply] at h1
    change _ = MvPolynomial.aeval v.1 F
    rw [show v.1 = _ from funext (hv v), TorsionZero.aeval_mul_of_isHomogeneous _ _ hF]
    refine Eq.trans ?_ (congrArg (· * c v ^ d) h1).symm
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have := Module.Finite.span_of_finite K (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

/- English proof (translation)
Introduce `h K _ _ P N J _ s d hN hd`. Take `⟨b, hb⟩` from `PowSec.exists_basis_sections h.globalSectionsRank K P (N * d) (Nat.mul_pos hN hd)`. Conclude with `hilb_cone_le_of_span P.A.hom P.L N d _ s b fun t => (hb t).exists`.
-/
theorem hilb_cone_le : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (s : J → (lbPow P.L N).Sec) (d : ℕ), 1 ≤ N → 1 ≤ d → hilb (cone P.A.hom (lbPow P.L N) s) d ≤ (N * d) ^ P.g := by
  intro h K _ _ P N J _ s d hN hd
  obtain ⟨b, hb⟩ := PowSec.exists_basis_sections h.globalSectionsRank K P (N * d) (Nat.mul_pos hN hd)
  exact hilb_cone_le_of_span P.A.hom P.L N d _ s b fun t => (hb t).exists

end GlobalTheory.AbelianFormCount
