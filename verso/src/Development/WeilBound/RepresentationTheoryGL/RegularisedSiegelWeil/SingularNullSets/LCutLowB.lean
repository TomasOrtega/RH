import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

/- English proof (translation)
The claim follows from `hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)`.
-/
theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

/- English proof (translation)
Rewrite using `[chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul, GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]`.
-/
theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) (γ : hermA D n)
    (hγ : γ ∈ ratHerm D n) (x : hermA D n) : chn ψ β (γ + x) = chn ψ β x := by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]`. Conclude with `hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _`.
-/
theorem per_nb {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n)
    (γ : hermA D n) (hγ : γ ∈ ratHerm D n) (x : hermA D n) : F (nb (γ + x) * g) = F (nb x * g) := by
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

/- English proof (translation)
The claim follows from `hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)`.
-/
theorem cont_nb {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

/- English proof (translation)
Use `show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))`. Rewrite using `[Matrix.trace_mul_comm]`.
-/
theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) (x : Mx D n n) (β : HermE D n) :
    pch ψ x (rat β.1) = ψ (GlobalTheory.CompanionTheory.FourierN.pr β.1 x) := by
  show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))
  rw [Matrix.trace_mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fc_eq (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam := rfl

/- English proof (translation)
Rewrite using `[chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Rewrite using `[show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]`. Normalize the expressions using the abelian group laws.
-/
theorem chn_shift (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b x : hermA D n) :
    chn ψ β b = chn ψ β (b + x) * pch ψ x.1 (rat β.1) := by
  rw [chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]
  abel

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Take `⟨hnb, hlam, hFD, -⟩` from `hC`. Take `⟨i1, i2, i3, i4, -, -⟩` from `GlobalTheory.TowerResNonzero.lattice_ratMx D n n`. Establish `: BorelSpace (Mx D n n)` using `⟨rfl⟩`. Establish `: BorelSpace (hermA D n)` using `Subtype.borelSpace _`. Establish `: SecondCountableTopology (hermA D n)` using `TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `: LocallyCompactSpace (hermA D n)` using `GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: DiscreteTopology (ratHerm D n)` using `GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm`. Establish `: Countable (ratHerm D n)` using `countable_of_Lindelof_of_discrete`. Establish `hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b` using `fun γ hγ b => by`. Rewrite using `[per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]`.

Establish `h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam` using `GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x`. Rewrite using `[fc_eq, fc_eq, ← h, ← integral_const_mul]`. Use `integral_congr_ae (.of_forall fun b => ?_)` and prove the remaining obligations. Use `show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))`. Rewrite using `[GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fc_nb_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) (β : HermE D n) (x : hermA D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β (nb x * g) = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  have hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b := fun γ hγ b => by
    rw [per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]
  have h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam :=
    GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x
  rw [fc_eq, fc_eq, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]
  ring

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Take `⟨hnb, hlam, hFD, h1⟩` from `hC`. Take `⟨i1, i2, i3, i4, -, -⟩` from `GlobalTheory.TowerResNonzero.lattice_ratMx D n n`. Establish `: BorelSpace (Mx D n n)` using `⟨rfl⟩`. Establish `: BorelSpace (hermA D n)` using `Subtype.borelSpace _`. Establish `: SecondCountableTopology (hermA D n)` using `TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `: LocallyCompactSpace (hermA D n)` using `GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: DiscreteTopology (ratHerm D n)` using `GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm`. Establish `: Countable (ratHerm D n)` using `countable_of_Lindelof_of_discrete`. Take `⟨K, hK, hcov⟩` from `GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)`. Take `⟨M, hM⟩` from `GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h) (per_nb hinv hnb h)`.

Use `Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top) ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]`. Conclude with `hM b`.
-/
theorem integrableOn_fc {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) (β : HermE D n) (h : G D n) :
    IntegrableOn (fun b => F (nb b * h) * chn ψ β b) 𝓖 lam := by
  obtain ⟨hnb, hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h)
    (per_nb hinv hnb h)
  refine Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top)
    ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)
  rw [norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]
  exact hM b

/- English proof (translation)
Rewrite using `[← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]`. Use `integral_congr_ae (.of_forall fun b => ?_)` and prove the remaining obligations. Use `show F (nb b * g) * _ = F (nb b * (nb x * g)) * _`. Rewrite using `[commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]`.
-/
theorem fc_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (β : HermE D n)
    {x : hermA D n} (hx : IntAt v x) {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb F β g = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  rw [← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * g) * _ = F (nb b * (nb x * g)) * _
  rw [commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]

/- English proof (translation)
Establish `e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b = ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b)` using `fun b => by`. Unfold `cutR`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cutF, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem fc_cutR {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (C : Cut D n v) (β : HermE D n) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  have e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b =
      ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) := fun b => by
    unfold cutR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]
  calc fc ψ lam 𝓖 nb (cutR nb C F) β g
      = ∫ b in 𝓖, ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_congr_ae (.of_forall e)
    _ = ∑ x ∈ C.s, ∫ b in 𝓖, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_finsetSum _ fun x _ => (integrableOn_fc hψ hC hF hinv β (nb x * g)).const_mul _
    _ = ∑ x ∈ C.s, C.co x * fc ψ lam 𝓖 nb F β (nb x * g) :=
        Finset.sum_congr rfl fun x _ => integral_const_mul _ _
    _ = ∑ x ∈ C.s, C.co x * (pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g) :=
        Finset.sum_congr rfl fun x _ => by rw [fc_nb_mul hψ hC hinv]
    _ = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
        rw [cutF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

end PositivityTheory.Rg.Rsw.L.LCutLow

end
