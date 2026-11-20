import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplit

/- English proof (translation)
Establish `hy' : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i)))))`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, p.sec_pr, p.sec_pr, map_mul, GlobalTheory.LatVac.cA_cA, ← add_mul]`. Conclude with `((GlobalTheory.FinPl.FrameLat.idem_iff p (y i)).1 (hy i)).symm`. Use `conv_lhs => rw [hy']`.

Rewrite using `[GlobalTheory.FinPl.FrameLat.decomp hL, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]`.
-/
theorem mem_latV_iff_wParts {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = p.v)) :
    y ∈ GlobalTheory.FinPl.latV S L (· = p.v) ↔ (fun i => p.sec (p.pr (y i))) ∈ GlobalTheory.FinPl.latV S L (· = p.v) ∧
      ∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = p.v) →
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * p.pr (cA D (y j)) ∈ 𝒪[k] := by
  have hy' : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    rw [Pi.add_apply, p.sec_pr, p.sec_pr, map_mul, GlobalTheory.LatVac.cA_cA, ← add_mul]
    exact ((GlobalTheory.FinPl.FrameLat.idem_iff p (y i)).1 (hy i)).symm
  conv_lhs => rw [hy']
  rw [GlobalTheory.FinPl.FrameLat.decomp hL, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]

/- English proof (translation)
Introduce `D k _ _ _ _ q S L L' hL hL' h`. Establish `key : ∀ (M M' : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → IsSelfDualC S M' → (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M' (· = q.v)) → ∀ y, y ∈ GlobalTheory.FinPl.latV S M (· = q.v …`. Introduce `M M' hM hM' hMM' y hy`. Establish `hs : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = q.v)` using `fun i => GlobalTheory.FinPl.FrameLat.latV_supp hy i`. Rewrite `hy` using `[mem_latV_iff_wParts q hM y hs]`.

Rewrite using `[mem_latV_iff_wParts q hM' y hs]`. Conclude with `⟨(hMM' _).1 hy.1, fun x hx => hy.2 x ((hMM' x).2 hx)⟩`. Use extensionality with `y`. Conclude with `⟨key L L' hL hL' h y, key L' L hL' hL (fun x => (h x).symm) y⟩`.
-/
theorem latV_eq_of_wPart : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L L' : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → IsSelfDualC S L' → (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v)) → GlobalTheory.FinPl.latV S L (· = q.v) = GlobalTheory.FinPl.latV S L' (· = q.v) := by
  intro D k _ _ _ _ q S L L' hL hL' h
  have key : ∀ (M M' : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → IsSelfDualC S M' →
      (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M' (· = q.v)) →
      ∀ y, y ∈ GlobalTheory.FinPl.latV S M (· = q.v) → y ∈ GlobalTheory.FinPl.latV S M' (· = q.v) := by
    intro M M' hM hM' hMM' y hy
    have hs : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = q.v) := fun i => GlobalTheory.FinPl.FrameLat.latV_supp hy i
    rw [mem_latV_iff_wParts q hM y hs] at hy
    rw [mem_latV_iff_wParts q hM' y hs]
    exact ⟨(hMM' _).1 hy.1, fun x hx => hy.2 x ((hMM' x).2 hx)⟩
  ext y
  exact ⟨key L L' hL hL' h y, key L' L hL' hL (fun x => (h x).symm) y⟩

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply]`. Rewrite using `[map_sum q.sec]`. Conclude with `Finset.sum_congr rfl fun j _ => GlobalTheory.SplitInt.mul_sec q _ _`.
-/
theorem rat_mulVec_sec (q : GlobalTheory.FinPl.SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (b : Fin n → k) :
    ((rat M : Mx D m n) *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map ((ofSplit q).π.comp (incA D)) *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => GlobalTheory.SplitInt.mul_sec q _ _

end

/- English proof (translation)
Introduce `D k _ _ _ _ q S A B o MS MA Y _ _ FA FS z hMS hMA ⟨LB₀, hLB₀⟩ hβA hβB hIS hIA`. Use `set f : D.host.E →+* k := (ofSplit q).π.comp (incA D) with hf`. Establish `hpr : (ofSplit q).pr = ⇑f` using `rfl`. Rewrite `hβA`, `hβB` using `[hpr]`. Establish `hc : Fintype.card (Y ⊕ Unit) = S.rank` using `FS.card_eq`.

Establish `hcA : Fintype.card Y = A.rank` using `FA.card_eq`. Establish `hB1 : B.rank = 1`. Use `o.rank_add` as an intermediate fact. Rewrite `hc` using `[Fintype.card_sum, hcA, Fintype.card_unit]`. Use linear arithmetic over natural numbers and integers.

Establish `hsub : ∀ i j : Fin B.rank, i = j` using `fun i j => Fin.ext (by omega)`. Use `haveI : Subsingleton (Fin B.rank) := ⟨hsub⟩`. Set `i₀ : Fin B.rank` to `⟨0, by omega⟩`. Establish `hcol : ∀ c : Y ⊕ Unit → k, FS.β *ᵥ c = o.iA.map f *ᵥ (FA.β *ᵥ fun a => c (Sum.inl a)) + c (Sum.inr ()) • (o.iB.map f *ᵥ z)`. Introduce `c`.

Use function extensionality and compare the values at `r`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, hβA, hβB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring`.

Conclude with `Finset.sum_congr rfl fun s _ => by ring`. Establish `hz : z i₀ ≠ 0`. Introduce `h0`. Establish `hz0 : z = 0` using `funext fun i => by rw [hsub i i₀, h0]; rfl`. Establish `h1` using `congrFun (congrFun FS.γβ (Sum.inr ())) (Sum.inr ())`.

Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Simplify using `only [hβB, hz0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1`. Conclude with `zero_ne_one h1`. Establish `hz' : ∀ i, z i ≠ 0` using `fun i => by rw [hsub i i₀]; exact hz`. Set `FB : Frame k B.rank Unit` to `{ β := Matrix.of fun i _ => z i γ := Matrix.of fun _ i => (z i)⁻¹ βγ := by`.

Use extensionality with `i j`. Rewrite using `[hsub j i]`. Simplify using `[Matrix.mul_apply, hz' i]`. Use `γβ := by`. Use extensionality with `u u'`.

Rewrite using `[Subsingleton.elim u' u]`. Simplify using `[Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, hz] }`. Take `⟨LB, hLB, -, hLBw⟩` from `GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D k q B Unit FB LB₀ hLB₀`. Take `⟨L', hL', hL'o⟩` from `GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o MA LB hMA hLB`. Establish `hFBv : ∀ y : k, (FB.β *ᵥ fun _ => y) = fun i => z i * y` using `fun y => by`.

Use function extensionality and compare the values at `i`. Simplify using `[FB, Matrix.mulVec, dotProduct]`. Use `⟨LB, hLB, ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `hqA : o.qA.map f * o.iA.map f = 1`. Rewrite using `[← Matrix.map_mul, o.qA_iA, Matrix.map_one _ (map_zero f) (map_one f)]`.

Establish `hqAB : o.qA.map f * o.iB.map f = 0`. Rewrite using `[← Matrix.map_mul, o.qA_iB, Matrix.map_zero _ (map_zero f)]`. Establish `hqB : o.qB.map f * o.iB.map f = 1`. Rewrite using `[← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hqBA : o.qB.map f * o.iA.map f = 0`.

Rewrite using `[← Matrix.map_mul, o.qB_iA, Matrix.map_zero _ (map_zero f)]`. Establish `hw : ∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S MS (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v)`. Introduce `x`. Use `set c := FS.γ *ᵥ x with hcdef`. Establish `hx : x = FS.β *ᵥ c` using `by rw [hcdef, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]`.

Establish `hqx : o.qA.map f *ᵥ x = FA.β *ᵥ fun a => c (Sum.inl a)`. Rewrite using `[hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iA.map f), hqA, Matrix.one_mulVec, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iB.map f), hqAB, Matrix.zero_mulVec, smul_zero, add_zero]`. Establish `hqBx : o.qB.map f *ᵥ x = FB.β *ᵥ fun _ => c (Sum.inr ())`. Rewrite using `[hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iA.map f), hqBA, Matrix.zero_mulVec, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iB.map f), hqB, Matrix.one_mulVec, zero_add, hFBv]`. Use function extensionality and compare the values at `i`.

Simplify using `[mul_comm]`. Establish `eS` using `hIS c`. Rewrite `eS` using `[← hx]`. Establish `eA` using `hIA (fun a => c (Sum.inl a))`. Establish `eB` using `hLBw (fun _ => c (Sum.inr ()))`.

Rewrite using `[← eS, hL'o q.v, show o.pA = rat o.qA from rfl, show o.pB = rat o.qB from rfl, rat_mulVec_sec, rat_mulVec_sec, ← hf, hqx, hqBx, ← eA, ← eB, Sum.forall]`. Introduce `y`. Rewrite using `[latV_eq_of_wPart D k q S MS L' hMS hL' hw]`. Conclude with `hL'o q.v y`. Use `hLBw (fun _ => y)` as an intermediate fact.

Rewrite `this` using `[hFBv]`. Conclude with `⟨fun h => this.1 fun _ => h, fun h => this.2 h ()⟩`.
-/
theorem exists_lineLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  intro D k _ _ _ _ q S A B o MS MA Y _ _ FA FS z hMS hMA ⟨LB₀, hLB₀⟩ hβA hβB hIS hIA
  set f : D.host.E →+* k := (ofSplit q).π.comp (incA D) with hf
  have hpr : (ofSplit q).pr = ⇑f := rfl
  rw [hpr] at hβA hβB
  have hc : Fintype.card (Y ⊕ Unit) = S.rank := FS.card_eq
  have hcA : Fintype.card Y = A.rank := FA.card_eq
  have hB1 : B.rank = 1 := by
    have := o.rank_add
    rw [Fintype.card_sum, hcA, Fintype.card_unit] at hc
    omega
  have hsub : ∀ i j : Fin B.rank, i = j := fun i j => Fin.ext (by omega)
  haveI : Subsingleton (Fin B.rank) := ⟨hsub⟩
  let i₀ : Fin B.rank := ⟨0, by omega⟩

  have hcol : ∀ c : Y ⊕ Unit → k, FS.β *ᵥ c =
      o.iA.map f *ᵥ (FA.β *ᵥ fun a => c (Sum.inl a)) + c (Sum.inr ()) • (o.iB.map f *ᵥ z) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, hβA, hβB,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring
    · exact Finset.sum_congr rfl fun s _ => by ring
  have hz : z i₀ ≠ 0 := by
    intro h0
    have hz0 : z = 0 := funext fun i => by rw [hsub i i₀, h0]; rfl
    have h1 := congrFun (congrFun FS.γβ (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [hβB, hz0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hz' : ∀ i, z i ≠ 0 := fun i => by rw [hsub i i₀]; exact hz
  let FB : Frame k B.rank Unit :=
    { β := Matrix.of fun i _ => z i
      γ := Matrix.of fun _ i => (z i)⁻¹
      βγ := by
        ext i j
        rw [hsub j i]
        simp [Matrix.mul_apply, hz' i]
      γβ := by
        ext u u'
        rw [Subsingleton.elim u' u]
        simp [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, hz] }
  obtain ⟨LB, hLB, -, hLBw⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D k q B Unit FB LB₀ hLB₀
  obtain ⟨L', hL', hL'o⟩ := GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o MA LB hMA hLB
  have hFBv : ∀ y : k, (FB.β *ᵥ fun _ => y) = fun i => z i * y := fun y => by
    funext i
    simp [FB, Matrix.mulVec, dotProduct]
  refine ⟨LB, hLB, ?_, fun y => ?_⟩
  ·
    have hqA : o.qA.map f * o.iA.map f = 1 := by
      rw [← Matrix.map_mul, o.qA_iA, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqAB : o.qA.map f * o.iB.map f = 0 := by
      rw [← Matrix.map_mul, o.qA_iB, Matrix.map_zero _ (map_zero f)]
    have hqB : o.qB.map f * o.iB.map f = 1 := by
      rw [← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqBA : o.qB.map f * o.iA.map f = 0 := by
      rw [← Matrix.map_mul, o.qB_iA, Matrix.map_zero _ (map_zero f)]
    have hw : ∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S MS (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v) := by
      intro x
      set c := FS.γ *ᵥ x with hcdef
      have hx : x = FS.β *ᵥ c := by rw [hcdef, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      have hqx : o.qA.map f *ᵥ x = FA.β *ᵥ fun a => c (Sum.inl a) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iA.map f), hqA,
          Matrix.one_mulVec, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iB.map f), hqAB, Matrix.zero_mulVec, smul_zero,
          add_zero]
      have hqBx : o.qB.map f *ᵥ x = FB.β *ᵥ fun _ => c (Sum.inr ()) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iA.map f), hqBA,
          Matrix.zero_mulVec, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iB.map f), hqB, Matrix.one_mulVec, zero_add,
          hFBv]
        funext i
        simp [mul_comm]
      have eS := hIS c
      rw [← hx] at eS
      have eA := hIA (fun a => c (Sum.inl a))
      have eB := hLBw (fun _ => c (Sum.inr ()))
      rw [← eS, hL'o q.v, show o.pA = rat o.qA from rfl, show o.pB = rat o.qB from rfl, rat_mulVec_sec,
        rat_mulVec_sec, ← hf, hqx, hqBx, ← eA, ← eB, Sum.forall]
    intro y
    rw [latV_eq_of_wPart D k q S MS L' hMS hL' hw]
    exact hL'o q.v y
  · have := hLBw (fun _ => y)
    rw [hFBv] at this
    exact ⟨fun h => this.1 fun _ => h, fun h => this.2 h ()⟩

end GlobalTheory.LineSplit
end
