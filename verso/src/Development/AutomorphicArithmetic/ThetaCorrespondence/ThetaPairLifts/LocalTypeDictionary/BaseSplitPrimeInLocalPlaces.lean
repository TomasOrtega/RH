import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangleStageFrameFactorisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvStageGeoConst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseMain
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealEmbeddingsOfCharactersOfSameExponent

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Helpers
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo
/- English proof (translation)
Establish `same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂` using `fun s c₁ c₂ hs g₁ g₂ => by`. Take `⟨k, hk⟩` from `H s s c₁ c₂ hs hs g₁ g₂`. Conclude with `mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)`. Establish `nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0` using `fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)`. Distinguish the cases in `ht : ∃ c, good t c`.

Take `⟨c₁, g₁⟩` from `ht`. Distinguish the cases in `hu : ∃ c, good u c`. Take `⟨c₂, g₂⟩` from `hu`. Take `⟨k, hk⟩` from `H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂`. Use `⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩` and prove the remaining obligations.

Introduce and unpack `s c (rfl | rfl) g`. Rewrite using `[div_mul_cancel₀ _ (nz _ _)]`. Conclude with `same _ _ _ (.inl rfl) g g₁`. Rewrite using `[same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]`. Take the linear combination `-hk`.

Use `⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `s c (rfl | rfl) g`. Rewrite using `[div_mul_cancel₀ _ (nz _ _)]`. Conclude with `same _ _ _ (.inl rfl) g g₁`. Conclude with `absurd ⟨c, g⟩ hu`.

Distinguish the cases in `hu : ∃ c, good u c`. Take `⟨c₂, g₂⟩` from `hu`. Use `⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `s c (rfl | rfl) g`. Conclude with `absurd ⟨c, g⟩ ht`.

Rewrite using `[div_mul_cancel₀ _ (nz _ _)]`. Conclude with `same _ _ _ (.inr rfl) g g₂`. Use `⟨0, 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `s c (rfl | rfl) g`. Conclude with `absurd ⟨c, g⟩ ht`.

Conclude with `absurd ⟨c, g⟩ hu`.
-/
private theorem common_factor_of_pair_relation {T K : Type} [Group K] {t u : T} (ν : T → K →* Circle) (lam : T → ℂ) (h0 : ∀ s, lam s ≠ 0)
    (good : T → ℂ → Prop)
    (H : ∀ s₁ s₂ c₁ c₂, (s₁ = t ∨ s₁ = u) → (s₂ = t ∨ s₂ = u) → good s₁ c₁ → good s₂ c₂ →
      ∃ k, (ν s₂ k : ℂ) * c₁ * lam s₂ = (ν s₁ k : ℂ) * c₂ * lam s₁) :
    ∃ (κ : ℂ) (k : K), ∀ s c, (s = t ∨ s = u) → good s c → c = κ * ((ν s k : ℂ) * lam s) := by
  have same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂ := fun s c₁ c₂ hs g₁ g₂ => by
    obtain ⟨k, hk⟩ := H s s c₁ c₂ hs hs g₁ g₂
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)
  have nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0 := fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)
  by_cases ht : ∃ c, good t c
  · obtain ⟨c₁, g₁⟩ := ht
    by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      obtain ⟨k, hk⟩ := H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂
      refine ⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · rw [same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]
        linear_combination -hk
    · refine ⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · exact absurd ⟨c, g⟩ hu
  · by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      refine ⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inr rfl) g g₂
    · refine ⟨0, 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · exact absurd ⟨c, g⟩ hu
/- English proof (translation)
Consider the cases of `X`. Consider the cases of `Y`. Consider the cases of `hJ`. Consider the cases of `hL`. Both sides reduce to the same expression.
-/
private theorem reSpace_eq_of_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {X Y : Spc F E n}
    (hJ : X.J = Y.J) (hL : X.L = Y.L) : reS X Y = Y := by
  cases X; cases Y; cases hJ; cases hL; rfl
/- English proof (translation)
Take `⟨R, Ra, h1⟩` from `hM F E σ B a a' Γ Xa oa oa' ha`. Take `⟨R', Rb, h2⟩` from `hM F E σ B a a' Γ Xb ob ob' hb`. Establish `h3 : IsMatched B Γ Xb ob ob' R Rb` using `⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩`. Take `⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩` from `(hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1`. Take `⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩` from `(hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3`.

Conclude with `⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩`.
-/
theorem exists_pivot_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
/- English proof (translation)
Use `⟨rfl, rfl, fun w => ⟨fun hw => ?_, ?_⟩, fun v hv => hU _ _ (hin v hv)⟩` and prove the remaining obligations. Establish `hv : w.under (𝓞 D.host.F) ∈ (GlobalTheory.SqStep.chs G i j s).T`. Distinguish the cases in `h0 : w ∈ G.pl.W0`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 h0`. Rewrite using `[G.pl.under_w hv]`.

Conclude with `Finset.mem_union_left _ hv`. Conclude with `Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, rfl⟩)`. Conclude with `⟨⟨_, hsub hv⟩, hv, GlobalTheory.FunObj.Good.under_injOn hL G s (hin ⟨_, hsub hv⟩ hv) hw (GlobalTheory.AdelicU.splitPrime_under _)⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `hin v hv`.
-/
private theorem readings_of_split_units {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (s : T) {Bs : Base D.host.F D.host.E}
    (hsub : (GlobalTheory.SqStep.chs G i j s).T ⊆ Bs.P)
    (hin : ∀ v : Bs.P, v.1 ∈ (GlobalTheory.SqStep.chs G i j s).T → GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G s)
    (hU : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G s → AUnit τ) :
    Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))
      (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
  classical
  refine ⟨rfl, rfl, fun w => ⟨fun hw => ?_, ?_⟩, fun v hv => hU _ _ (hin v hv)⟩
  · have hv : w.under (𝓞 D.host.F) ∈ (GlobalTheory.SqStep.chs G i j s).T := by
      by_cases h0 : w ∈ G.pl.W0
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        rw [G.pl.under_w hv]
        exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, rfl⟩)
    exact ⟨⟨_, hsub hv⟩, hv, GlobalTheory.FunObj.Good.under_injOn hL G s (hin ⟨_, hsub hv⟩ hv) hw (GlobalTheory.AdelicU.splitPrime_under _)⟩
  · rintro ⟨v, hv, rfl⟩
    exact hin v hv
/- English proof (translation)
Rewrite `hv` using `[GlobalTheory.SqStepArith.chs_T_base G hL i j]`. Establish `hw : G.pl.w v.1 ∈ G.pl.W0` using `Finset.mem_image_of_mem _ hv`. Establish `h1` using `hB.2.2.2 v (Finset.mem_union_left _ hv)`. Establish `e` using `GlobalTheory.FunObj.Good.under_injOn hL G t h1 (Finset.mem_union_left _ hw) ((GlobalTheory.AdelicU.splitPrime_under _).trans (G.pl.under_w hv).symm)`. Rewrite using `[e]`.

Conclude with `Finset.mem_union_left _ hw`.
-/
private theorem base_split_prime_in_local_places {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) {W : G.Weil} {i j : Fin D.R.m} {t : T}
    {Bs : Base D.host.F D.host.E} (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (v : Bs.P) (hv : v.1 ∈ (GlobalTheory.SqStep.chs G i j μ₀).T) :
    GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G μ₀ := by
  classical
  rw [GlobalTheory.SqStepArith.chs_T_base G hL i j] at hv
  have hw : G.pl.w v.1 ∈ G.pl.W0 := Finset.mem_image_of_mem _ hv
  have h1 := hB.2.2.2 v (Finset.mem_union_left _ hv)
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t h1 (Finset.mem_union_left _ hw)
    ((GlobalTheory.AdelicU.splitPrime_under _).trans (G.pl.under_w hv).symm)
  rw [e]
  exact Finset.mem_union_left _ hw
/- English proof (translation)
Take `⟨⟨r1, -, l1⟩, ⟨r2, -, l2⟩, r3, j3, l3⟩` from `hO`. Establish `L1 : Γ.V.L = Γ₀.V.L` using `Submodule.ext fun y => (l1 y).trans (h.latA.1 y).symm`. Establish `L2 : Γ.V'.L = Γ₀.V'.L` using `Submodule.ext fun y => (l2 y).trans (h.latB.1 y).symm`. Establish `L3 : Γ.W.L = Γ₀.W.L` using `Submodule.ext fun y => (l3 y).trans (h.latA.2 y).symm`. Establish `J3 : Γ.W.J = Γ₀.W.J` using `j3.trans h.pairA.JW.symm`.

Establish `e1 : reS Γ.V Γ₀.V = Γ₀.V` using `reSpace_eq_of_same (JA.trans h.JA.symm) L1`. Establish `e2 : reS Γ.V' Γ₀.V' = Γ₀.V'` using `reSpace_eq_of_same (JB.trans h.JB.symm) L2`. Establish `e3 : reS Γ.W Γ₀.W = Γ₀.W` using `reSpace_eq_of_same J3 L3`. Establish `hV : (reS Γ.V Γ₀.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p` using `by rw [e1, ← ep]; exact g₀.hV`. Establish `hV' : (reS Γ.V' Γ₀.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q)` using `by rw [e2, ← eq]; exact g₀.hV'`.

Establish `hW : (reS Γ.W Γ₀.W).IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (Γ.p + Γ.q)) (Γ.p + Γ.q)`. Rewrite using `[e3, ← ep, ← eq]`. Conclude with `g₀.hW`. Establish `G : (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs` using `⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hW, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩`. Use `⟨G, ⟨h.pairA.base, h.pairA.psi, JA, J3.trans h.pairA.JW, ⟨_, _, hV⟩, ⟨_, _, hW⟩, G.hM⟩, ⟨h.pairB.base, h.pairB.psi, JB, J3.trans h.pairB.JW, ⟨_, _, hV'⟩, ⟨_, _, hW⟩, G.hM'⟩, ⟨l1, l3⟩, ⟨l2, l3⟩, h.cartA, h.cartB, JA, JB, m1, d1, m2, d2, h.basA, h.basB, h.basW⟩` and prove the remaining obligations.
-/
private theorem stage_regular_geometry {ψ : AddChar (AF D.host.F) ℂ} {A A' WW : HSp D} {X : Tri T A A' WW} {FA : GlobalTheory.ChainFr.Fr A}
    {FA' : GlobalTheory.ChainFr.Fr A'} {FW : GlobalTheory.ChainFr.Fr WW} {hr : A.rank + A'.rank = WW.rank} {Bs : Base D.host.F D.host.E}
    {Γ Γ₀ : Geo D.sp.cm.sig A.rank A'.rank} (hO : GlobalTheory.SqStepBig.Over X Γ) (g : Γ.IsGood Bs) (g₀ : Γ₀.IsGood Bs)
    (ep : Γ₀.p = Γ.p) (eq : Γ₀.q = Γ.q) (h : IsStageGeo ψ X FA FA' FW hr Bs Γ₀)
    (JA : Γ.V.J = (1 : D.host.E) • A.gram) (JB : Γ.V'.J = (-1 : D.host.E) • A'.gram)
    (m1 : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)) (d1 : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd)
    (m2 : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)) (d2 : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd') :
    (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs ∧ IsStageGeo ψ X FA FA' FW hr Bs (reG Γ Γ₀.V Γ₀.V' Γ₀.W) := by
  obtain ⟨⟨r1, -, l1⟩, ⟨r2, -, l2⟩, r3, j3, l3⟩ := hO
  have L1 : Γ.V.L = Γ₀.V.L := Submodule.ext fun y => (l1 y).trans (h.latA.1 y).symm
  have L2 : Γ.V'.L = Γ₀.V'.L := Submodule.ext fun y => (l2 y).trans (h.latB.1 y).symm
  have L3 : Γ.W.L = Γ₀.W.L := Submodule.ext fun y => (l3 y).trans (h.latA.2 y).symm
  have J3 : Γ.W.J = Γ₀.W.J := j3.trans h.pairA.JW.symm
  have e1 : reS Γ.V Γ₀.V = Γ₀.V := reSpace_eq_of_same (JA.trans h.JA.symm) L1
  have e2 : reS Γ.V' Γ₀.V' = Γ₀.V' := reSpace_eq_of_same (JB.trans h.JB.symm) L2
  have e3 : reS Γ.W Γ₀.W = Γ₀.W := reSpace_eq_of_same J3 L3
  have hV : (reS Γ.V Γ₀.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := by rw [e1, ← ep]; exact g₀.hV
  have hV' : (reS Γ.V' Γ₀.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := by rw [e2, ← eq]; exact g₀.hV'
  have hW : (reS Γ.W Γ₀.W).IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (Γ.p + Γ.q)) (Γ.p + Γ.q) := by
    rw [e3, ← ep, ← eq]; exact g₀.hW
  have G : (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs :=
    ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hW, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩
  refine ⟨G, ⟨h.pairA.base, h.pairA.psi, JA, J3.trans h.pairA.JW, ⟨_, _, hV⟩, ⟨_, _, hW⟩, G.hM⟩,
    ⟨h.pairB.base, h.pairB.psi, JB, J3.trans h.pairB.JW, ⟨_, _, hV'⟩, ⟨_, _, hW⟩, G.hM'⟩, ⟨l1, l3⟩, ⟨l2, l3⟩, h.cartA, h.cartB,
    JA, JB, m1, d1, m2, d2, h.basA, h.basB, h.basW⟩
end Helpers
/- English proof (translation)
Introduce `hP hK hM`. Take `⟨a1, h1⟩` from `GlobalTheory.T.towerStage_seesawDictionary_framesSignatures`. Take `⟨a2, h2⟩` from `GlobalTheory.StageGeo.aUnit_locPl`. Use `⟨max a1 a2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨c1, x1, g1⟩` from `h1 ε CF (le_of_max_le_left hCF)`.

Take `⟨c2, x2, g2⟩` from `h2 ε CF (le_of_max_le_right hCF)`. Use `⟨max c1 c2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩` and prove the remaining obligations. Establish `q1` using `g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G`. Establish `q2` using `g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G`. Introduce `W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P' hint`.

Take `⟨F₀, F₀', FW₀, a, b, -, -, -, hd⟩` from `q1 W i j p q A A' WW X hX`. Take `⟨-, -, -, -, nA, nA', nW, hXi⟩` from `hX`. Establish `b1` using `hg.eBig`. Establish `b2` using `hg.aBig`. Establish `b3` using `hg.lt`.

Establish `b4` using `hg.even`. Rewrite `b1`, `b2` using `[hp, hq]`. Take `⟨Γ₀, p₀, q₀, g₀, s₀⟩` from `UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X F₀ F₀' FW₀ hXi.rank Bs p q hB.2.1 hB.1.1 hB.2.2.1 hXi.rigA hXi.rigA' hXi.rigW hXi.meas hXi.meas' nA nA' nW b4 (by omega) b2 hg.kappa`. Establish `rd : ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.StageGeo.Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s)`. Introduce and unpack `s (rfl | rfl)`.

Conclude with `readings_of_split_units hL i j _ hB.1.2.1 hB.1.2.2.2 (q2 _)`. Conclude with `readings_of_split_units hL i j _ hB.2.2.2.2.1.sub (base_split_prime_in_local_places hL hB.1) (q2 _)`. Take `⟨κ, k, hκ⟩` from `common_factor_of_pair_relation (t := t) (u := μ₀) (fun s => (GlobalTheory.SqStep.chs G i j s).ν) lam hF.1 (fun s c => ∃ om om' Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf ∧ GlobalTheory.IndefiniteRowSid …`. Introduce and unpack `s₁ s₂ c₁ c₂ h₁ h₂ ⟨o₁, o₁', R₁, m₁, k₁⟩ ⟨o₂, o₂', R₂, m₂, k₂⟩`. Take `⟨e, cA, cB, hv⟩` from `(hs s₁ h₁).2.2.2.2 o₁ o₁' m₁.triple`.

Apply the tactic sequence `obtain ⟨G₂, S₂⟩ := stage_regular_geometry hO hg g₀ (p₀.trans hp.symm) (q₀.trans hq.symm) s₀ hv.JW hv.JW₁ hv.measW hv.domW hv.measW₁ hv.domW₁`. Establish `t₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₁) o₁ o₁'` using `⟨m₁.triple.base, G₂, m₁.triple.chars, m₁.triple.weil, m₁.triple.weil'⟩`. Establish `t₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₂) o₂ o₂'` using `⟨m₂.triple.base, G₂, m₂.triple.chars, m₂.triple.weil, m₂.triple.weil'⟩`. Take `⟨R', Sa, Sb, da, db, n₁, n₂, l₁, l₂, hdb⟩` from `_root_.exists_pivot_pair hP hK hM t₁ t₂`. Establish `E1` using `_root_.GlobalTheory.StageGeo.geometric_stage_constant_ratio hP hK hM hXi S₂ hd hF (rd s₁ h₁) (rd s₂ h₂) n₁ n₂ l₁ l₂`.

Take `⟨k, E2⟩` from `_root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m₁ m₂ n₁ n₂ k₁ k₂ l₁ l₂`. Use `⟨k⁻¹, ?_⟩` and prove the remaining obligations. Establish `z₁ : (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) ≠ 0` using `Circle.coe_ne_zero _`. Establish `z₂ : (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) ≠ 0` using `Circle.coe_ne_zero _`. Rewrite `E2` using `[Circle.coe_div]`.

Rewrite using `[map_inv, map_inv, Circle.coe_inv, Circle.coe_inv]`. Generalize the expression as in `(((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) = n₁ at z₁ E2 ⊢`. Generalize the expression as in `(((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) = n₂ at z₂ E2 ⊢`. Establish `E3 : da * c₂ * n₂ = n₁ * (db * c₁)` using `by rw [E2]; field_simp`. Establish `E4 : n₁ * c₁ * lam s₂ = n₂ * c₂ * lam s₁` using `mul_left_cancel₀ hdb (by linear_combination (-lam s₂) * E3 + c₂ * n₂ * E1)`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨-, Pm, pp, pp', J, hsurj, -, -, hI, hI', -⟩` from `hF`. Take `⟨P, eP⟩` from `hsurj (κ • pp' P')`. Use `⟨P, k, fun s hs' om om' Rf c m kc h => ?_⟩` and prove the remaining obligations. Rewrite using `[hI, hI' s P' (hint s hs'), eP, map_smul, hκ s c hs' ⟨om, om', Rf, m, kc⟩]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.T.pivot_reduction_divisibility : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ → Γ.p = p → Γ.q = q → Γ.IsGood Bs →
        (∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s) →
        ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank A'.rank) (P' : PolF D WW.rank A'.rank),
          (∀ s, (s = t ∨ s = μ₀) → ∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ s P' h) X.fd' X.m') →
          ∃ (P : PolF D WW.rank A.rank) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∀ s, (s = t ∨ s = μ₀) →
            ∀ om om' Rf (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
              ∀ h, ((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * X.I W.ψ W.θ s P h = c * X.I' W.ψ W.θ s P' h := by
  intro hP hK hM
  obtain ⟨a1, h1⟩ := GlobalTheory.T.towerStage_seesawDictionary_framesSignatures
  obtain ⟨a2, h2⟩ := GlobalTheory.StageGeo.aUnit_locPl
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have q1 := g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  have q2 := g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  intro W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P' hint
  obtain ⟨F₀, F₀', FW₀, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨-, -, -, -, nA, nA', nW, hXi⟩ := hX
  have b1 := hg.eBig
  have b2 := hg.aBig
  have b3 := hg.lt
  have b4 := hg.even
  rw [hp, hq] at b1 b2
  obtain ⟨Γ₀, p₀, q₀, g₀, s₀⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X F₀ F₀' FW₀ hXi.rank Bs p q hB.2.1 hB.1.1 hB.2.2.1
    hXi.rigA hXi.rigA' hXi.rigW hXi.meas hXi.meas' nA nA' nW b4 (by omega) b2 hg.kappa
  have rd : ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.StageGeo.Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
    rintro s (rfl | rfl)
    · exact readings_of_split_units hL i j _ hB.1.2.1 hB.1.2.2.2 (q2 _)
    · exact readings_of_split_units hL i j _ hB.2.2.2.2.1.sub (base_split_prime_in_local_places hL hB.1) (q2 _)
  obtain ⟨κ, k, hκ⟩ := common_factor_of_pair_relation (t := t) (u := μ₀) (fun s => (GlobalTheory.SqStep.chs G i j s).ν) lam hF.1
    (fun s c => ∃ om om' Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c) (by
    rintro s₁ s₂ c₁ c₂ h₁ h₂ ⟨o₁, o₁', R₁, m₁, k₁⟩ ⟨o₂, o₂', R₂, m₂, k₂⟩
    obtain ⟨e, cA, cB, hv⟩ := (hs s₁ h₁).2.2.2.2 o₁ o₁' m₁.triple
    obtain ⟨G₂, S₂⟩ := stage_regular_geometry hO hg g₀ (p₀.trans hp.symm) (q₀.trans hq.symm) s₀ hv.JW hv.JW₁ hv.measW hv.domW hv.measW₁ hv.domW₁
    have t₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₁) o₁ o₁' :=
      ⟨m₁.triple.base, G₂, m₁.triple.chars, m₁.triple.weil, m₁.triple.weil'⟩
    have t₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₂) o₂ o₂' :=
      ⟨m₂.triple.base, G₂, m₂.triple.chars, m₂.triple.weil, m₂.triple.weil'⟩
    obtain ⟨R', Sa, Sb, da, db, n₁, n₂, l₁, l₂, hdb⟩ := _root_.exists_pivot_pair hP hK hM t₁ t₂
    have E1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_ratio hP hK hM hXi S₂ hd hF (rd s₁ h₁) (rd s₂ h₂) n₁ n₂ l₁ l₂
    obtain ⟨k, E2⟩ := _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m₁ m₂ n₁ n₂ k₁ k₂ l₁ l₂
    refine ⟨k⁻¹, ?_⟩
    have z₁ : (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have z₂ : (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [Circle.coe_div] at E2
    rw [map_inv, map_inv, Circle.coe_inv, Circle.coe_inv]
    generalize (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) = n₁ at z₁ E2 ⊢
    generalize (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) = n₂ at z₂ E2 ⊢
    have E3 : da * c₂ * n₂ = n₁ * (db * c₁) := by rw [E2]; field_simp
    have E4 : n₁ * c₁ * lam s₂ = n₂ * c₂ * lam s₁ :=
      mul_left_cancel₀ hdb (by linear_combination (-lam s₂) * E3 + c₂ * n₂ * E1)
    calc n₂⁻¹ * c₁ * lam s₂ = n₁⁻¹ * n₂⁻¹ * (n₁ * c₁ * lam s₂) := by field_simp
      _ = n₁⁻¹ * c₂ * lam s₁ := by rw [E4]; field_simp)
  obtain ⟨-, Pm, pp, pp', J, hsurj, -, -, hI, hI', -⟩ := hF
  obtain ⟨P, eP⟩ := hsurj (κ • pp' P')
  refine ⟨P, k, fun s hs' om om' Rf c m kc h => ?_⟩
  rw [hI, hI' s P' (hint s hs'), eP, map_smul, hκ s c hs' ⟨om, om', Rf, m, kc⟩]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
