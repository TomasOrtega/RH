import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlattenMany
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSummandOfQuot
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamGood1

open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

section Span

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

/- English proof (translation)
Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Conclude with `hL a ha e (hS e he)`.
-/
theorem span_le {S : Set E} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hS : ∀ e ∈ S, e ∈ L) : spanOver R S ≤ L := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hL a ha e (hS e he)

/- English proof (translation)
Introduce `_ ha _ hv` and use `smul_mem_spanOver R S ha hv`.
-/
theorem span_stable (S : Set E) : ∀ a ∈ R, ∀ v ∈ spanOver R S, a • v ∈ spanOver R S :=
  fun _ ha _ hv => smul_mem_spanOver R S ha hv

/- English proof (translation)
The claim follows from `le_antisymm (span_le R hL fun _ h => h) fun _ h => mem_spanOver_of_mem R h`.
-/
theorem span_self {L : AddSubgroup E} (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) :
    spanOver R (L : Set E) = L :=
  le_antisymm (span_le R hL fun _ h => h) fun _ h => mem_spanOver_of_mem R h

/- English proof (translation)
Unfold `spanOver`. Rewrite using `[AddMonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨a, ha, e, he, rfl⟩, rfl⟩`. Conclude with `⟨a, ha, f e, ⟨e, he, rfl⟩, by simp⟩`. Introduce and unpack `⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩`. Conclude with `⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩`.
-/
theorem map_span (f : E →ₗ[Ω] E') (S : Set E) :
    (spanOver R S).map f.toAddMonoidHom = spanOver R (f '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, f e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

/- English proof (translation)
Introduce `a ha v hv`. Take `⟨y, hy, z, hz, rfl⟩` from `AddSubgroup.mem_sup.1 hv`. Rewrite using `[smul_add]`. Conclude with `AddSubgroup.add_mem_sup (hA a ha y hy) (hB a ha z hz)`.
-/
theorem sup_stable {A B : AddSubgroup E} (hA : ∀ a ∈ R, ∀ v ∈ A, a • v ∈ A)
    (hB : ∀ a ∈ R, ∀ v ∈ B, a • v ∈ B) : ∀ a ∈ R, ∀ v ∈ A ⊔ B, a • v ∈ A ⊔ B := by
  intro a ha v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
  rw [smul_add]
  exact AddSubgroup.add_mem_sup (hA a ha y hy) (hB a ha z hz)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `span_le R (sup_stable R (span_stable R S) (span_stable R T)) ?_` and prove the remaining obligations. Introduce and unpack `e (he | he)`. Conclude with `AddSubgroup.mem_sup_left (mem_spanOver_of_mem R he)`. Conclude with `AddSubgroup.mem_sup_right (mem_spanOver_of_mem R he)`.

Conclude with `sup_le (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inl he)) (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inr he))`.
-/
theorem span_union (S T : Set E) : spanOver R (S ∪ T) = spanOver R S ⊔ spanOver R T := by
  apply le_antisymm
  · refine span_le R (sup_stable R (span_stable R S) (span_stable R T)) ?_
    rintro e (he | he)
    · exact AddSubgroup.mem_sup_left (mem_spanOver_of_mem R he)
    · exact AddSubgroup.mem_sup_right (mem_spanOver_of_mem R he)
  · exact sup_le (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inl he))
      (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inr he))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `span_le R' (span_stable R' _) fun e he => span_le R (fun a ha => span_stable R' S a (h ha)) (fun _ h => mem_spanOver_of_mem R' h) he`. Conclude with `span_le R' (span_stable R' _) fun e he => mem_spanOver_of_mem R' (mem_spanOver_of_mem R he)`.
-/
theorem span_span {R' : Subalgebra o Ω} (h : R ≤ R') (S : Set E) :
    spanOver R' (spanOver R S : Set E) = spanOver R' S := by
  apply le_antisymm
  · exact span_le R' (span_stable R' _) fun e he =>
      span_le R (fun a ha => span_stable R' S a (h ha)) (fun _ h => mem_spanOver_of_mem R' h) he
  · exact span_le R' (span_stable R' _) fun e he =>
      mem_spanOver_of_mem R' (mem_spanOver_of_mem R he)

/- English proof (translation)
Take `⟨-, k, φ, v, hv, hφ, hs⟩` from `PositivityTheory.Xgn.A_summand_of_quot.exists_dual R h`. Use `⟨Finset.univ.image v, le_antisymm (fun e he => ?_) (span_le R h.1 ?_), ?_⟩` and prove the remaining obligations. Rewrite using `[← hs e]`. Conclude with `sum_mem fun i _ => smul_mem_spanOver R _ (hφ i e he) (mem_spanOver_of_mem R (by simp))`. Introduce `e he`.

Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at he`. Take `⟨i, rfl⟩` from `he`. Conclude with `hv i`. Rewrite using `[eq_top_iff]`. Introduce `e _`.

Rewrite using `[← hs e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`.
-/
theorem fg_of_locFree {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) :
    ∃ S : Finset E, L = spanOver R (S : Set E) ∧ Submodule.span Ω (S : Set E) = ⊤ := by
  classical
  obtain ⟨-, k, φ, v, hv, hφ, hs⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R h
  refine ⟨Finset.univ.image v, le_antisymm (fun e he => ?_) (span_le R h.1 ?_), ?_⟩
  · rw [← hs e]
    exact sum_mem fun i _ => smul_mem_spanOver R _ (hφ i e he) (mem_spanOver_of_mem R (by simp))
  · intro e he
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at he
    obtain ⟨i, rfl⟩ := he
    exact hv i
  · rw [eq_top_iff]
    intro e _
    rw [← hs e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/- English proof (translation)
Set `e` to `Submodule.quotEquivOfEqBot (⊥ : Submodule Ω E) rfl`. Use `locFree_baseChange R R (fun a ha => ha) e.toLinearMap (IsBaseChange.ofEquiv e) r _ h` as an intermediate fact. Establish `h2 : (e.toLinearMap '' (L.map (⊥ : Submodule Ω E).mkQ.toAddMonoidHom : Set _)) = (L : Set E)`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨w, hw, rfl⟩, rfl⟩`. Simplify `hw` using `[e]`. Introduce `hv`. Conclude with `⟨_, ⟨v, hv, rfl⟩, by simp [e]⟩`. Rewrite `this` using `[h2, span_self R hL]`. Then use the resulting hypothesis.
-/
theorem locFree_of_bot {r : ℕ} {L : AddSubgroup E} (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L)
    (h : LocFree R r (L.map (⊥ : Submodule Ω E).mkQ.toAddMonoidHom)) : LocFree R r L := by
  let e := Submodule.quotEquivOfEqBot (⊥ : Submodule Ω E) rfl
  have := locFree_baseChange R R (fun a ha => ha) e.toLinearMap (IsBaseChange.ofEquiv e) r _ h
  have h2 : (e.toLinearMap '' (L.map (⊥ : Submodule Ω E).mkQ.toAddMonoidHom : Set _)) = (L : Set E) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa [e] using hw
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, by simp [e]⟩
  rwa [h2, span_self R hL] at this

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `: (DistribMulAction.toAddMonoidHom (J → Ω) c) v = ∑ j, v j • (Pi.single j c : J → Ω)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, mul_comm]`.

Rewrite using `[this]`. Conclude with `sum_mem fun j _ => smul_mem_spanOver R _ (hv j (Set.mem_univ j)) (mem_spanOver_of_mem R ⟨j, rfl⟩)`. Use `span_le R ?_ ?_` and prove the remaining obligations. Introduce and unpack `a ha _ ⟨v, hv, rfl⟩`. Use `⟨a • v, fun j _ => R.mul_mem ha (hv j (Set.mem_univ j)), ?_⟩` and prove the remaining obligations.

Simplify using `[smul_comm a c]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨Pi.single j 1, fun i _ => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `using R.one_mem`. Simplify `R.zero_mem` using `[h]`. Use extensionality with `i`. Simplify using `[Pi.single_apply]`.
-/
theorem mulLat_std (c : Ω) (J : Type) [Fintype J] [DecidableEq J] :
    mulLat c (stdLat R J) = spanOver R (Set.range fun j : J => (Pi.single j c : J → Ω)) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have : (DistribMulAction.toAddMonoidHom (J → Ω) c) v = ∑ j, v j • (Pi.single j c : J → Ω) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact sum_mem fun j _ => smul_mem_spanOver R _ (hv j (Set.mem_univ j))
      (mem_spanOver_of_mem R ⟨j, rfl⟩)
  · refine span_le R ?_ ?_
    · rintro a ha _ ⟨v, hv, rfl⟩
      refine ⟨a • v, fun j _ => R.mul_mem ha (hv j (Set.mem_univ j)), ?_⟩
      simp [smul_comm a c]
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, fun i _ => ?_, ?_⟩
      · by_cases h : i = j
        · subst h; simpa using R.one_mem
        · simpa [h] using R.zero_mem
      · ext i
        simp [Pi.single_apply]

end Span

section Fam

variable (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω)
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

/- English proof (translation)
Establish `hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t` using `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _`. Unfold `chartRing at ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨u, rfl⟩` from `hy`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t`. Rewrite using `[pow_one, mul_comm, div_mul_div_cancel₀ hs]`. Use `beta_reduce`. Rewrite using `[this]`.

Conclude with `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _`. Consider the case `algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩`. Consider the case `add a b _ _ ha hb => exact frac_add _ hf ha hb`. Consider the case `mul a b _ _ ha hb`. Take `⟨m, hm⟩` from `ha`.

Take `⟨n, hn⟩` from `hb`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Use `Subalgebra.mul_mem _ hm hn` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_trans {s t : ∀ k, ι k} (hs : mseg x s ≠ 0) {a : Ω} (ha : a ∈ chartRing O (mseg x) s) :
    ∃ m : ℕ, (mseg x s / mseg x t) ^ m * a ∈ chartRing O (mseg x) t := by
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  unfold chartRing at ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
      rw [pow_one, mul_comm, div_mul_div_cancel₀ hs]
    beta_reduce
    rw [this]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb => exact frac_add _ hf ha hb
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have := Subalgebra.mul_mem _ hm hn
    convert this using 1
    ring

/- English proof (translation)
Use `⟨fun s _ => span_stable _ S, fun s t hs _ v hv => ?_⟩` and prove the remaining obligations. Establish `hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t` using `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, e, he, rfl⟩` from `hy`.

Take `⟨m, hm⟩` from `chart_trans O x (t := t) hs ha`. Conclude with `⟨m, by rw [smul_smul]; exact smul_mem_spanOver _ _ hm (mem_spanOver_of_mem _ he)⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add a b _ _ ha hb => exact loc_add _ _ (span_stable _ S) hf ha hb`. Consider the case `neg a _ ha`.

Take `⟨m, hm⟩` from `ha`. Conclude with `⟨m, by rw [smul_neg]; exact neg_mem hm⟩`.
-/
theorem fam_span (S : Set E) : IsLatFamily O x fun c => spanOver (chartRing O (mseg x) c) S := by
  refine ⟨fun s _ => span_stable _ S, fun s t hs _ v hv => ?_⟩
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, e, he, rfl⟩ := hy
    obtain ⟨m, hm⟩ := chart_trans O x (t := t) hs ha
    exact ⟨m, by rw [smul_smul]; exact smul_mem_spanOver _ _ hm (mem_spanOver_of_mem _ he)⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb => exact loc_add _ _ (span_stable _ S) hf ha hb
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

/- English proof (translation)
Use `⟨fun s hs => sup_stable _ (hA.1 s hs) (hB.1 s hs), fun s t hs ht v hv => ?_⟩` and prove the remaining obligations. Establish `hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t` using `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _`. Take `⟨y, hy, z, hz, rfl⟩` from `AddSubgroup.mem_sup.1 hv`. Take `⟨m, hm⟩` from `hA.2 s t hs ht y hy`. Take `⟨n, hn⟩` from `hB.2 s t hs ht z hz`.

Conclude with `loc_add _ _ (sup_stable _ (hA.1 t ht) (hB.1 t ht)) hf ⟨m, AddSubgroup.mem_sup_left hm⟩ ⟨n, AddSubgroup.mem_sup_right hn⟩`.
-/
theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup E} (hA : IsLatFamily O x A) (hB : IsLatFamily O x B) :
    IsLatFamily O x fun c => A c ⊔ B c := by
  refine ⟨fun s hs => sup_stable _ (hA.1 s hs) (hB.1 s hs), fun s t hs ht v hv => ?_⟩
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
  obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
  obtain ⟨n, hn⟩ := hB.2 s t hs ht z hz
  exact loc_add _ _ (sup_stable _ (hA.1 t ht) (hB.1 t ht)) hf
    ⟨m, AddSubgroup.mem_sup_left hm⟩ ⟨n, AddSubgroup.mem_sup_right hn⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `s hs a ha _ ⟨v, hv, rfl⟩`. Conclude with `⟨a • v, hA.1 s hs a ha v hv, by simp⟩`. Introduce and unpack `s t hs ht _ ⟨v, hv, rfl⟩`. Take `⟨m, hm⟩` from `hA.2 s t hs ht v hv`.

Conclude with `⟨m, _, hm, by simp⟩`.
-/
theorem fam_map {A : (∀ k, ι k) → AddSubgroup E} (hA : IsLatFamily O x A) (f : E →ₗ[Ω] E') :
    IsLatFamily O x fun c => (A c).map f.toAddMonoidHom := by
  refine ⟨?_, ?_⟩
  · rintro s hs a ha _ ⟨v, hv, rfl⟩
    exact ⟨a • v, hA.1 s hs a ha v hv, by simp⟩
  · rintro s t hs ht _ ⟨v, hv, rfl⟩
    obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv
    exact ⟨m, _, hm, by simp⟩

end Fam

/- English proof (translation)
Set `W : Bool × I → Submodule Ω E` to `fun q => if q.1 then U q.2 else ⊥`. Take `⟨K', i1, i2, ι', i3, z, hz, hfree⟩` from `PositivityTheory.Xgn.t_flatten_many O Ω K ι x d hm hf (Bool × I) (fun q => Module.finrank Ω (E ⧸ W q)) (fun q => E ⧸ W q) (fun q c => (Γ q.2 c).map (W q).mkQ.toAddMonoidHom) (fun q => ⟨rfl, fam_map O x (hΓ q.2).1 _, by`. Introduce `c hc`. Take `⟨S, hS, hT⟩` from `(hΓ q.2).2 c hc`. Use `⟨S.image (W q).mkQ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hS, map_span, Finset.coe_image]`. Rewrite using `[Finset.coe_image, ← Submodule.map_span, hT, Submodule.map_top, Submodule.range_mkQ]⟩)`. Use `⟨K', i1, i2, ι', i3, z, hz, fun j c hc => ?_⟩` and prove the remaining obligations. Establish `key : ∀ q : Bool × I, LocFree (chartRing O (mseg (joinCoord x z)) c) (Module.finrank Ω (E ⧸ W q)) ((spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ q.2 (restrictChart c) : Set E)).map (W q).mkQ.toAddMonoidHom)`. Introduce `q`.

Rewrite using `[map_span]`. Conclude with `hfree q c hc`. Establish `h0` using `locFree_of_bot _ (span_stable _ _) (key (false, j))`. Establish `h1` using `h0`. Rewrite `h1` using `[← (PositivityTheory.Xgn.A_summand_of_quot.exists_dual _ h0).1]`.

Conclude with `⟨h1, (PositivityTheory.Xgn.summand_iff_locFree_quot _ (U j) _ _ _ h1).1 (key (true, j))⟩`.
-/
theorem flatten_summand (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ)
    (hm : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    (hf : fnField O x = ⊤) (I : Type) [Fintype I] (E : Type) [AddCommGroup E] [Module Ω E]
    (U : I → Submodule Ω E) (Γ : I → (∀ k, ι k) → AddSubgroup E)
    (hΓ : ∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset E,
      Γ j c = spanOver (chartRing O (mseg x) c) (S : Set E) ∧ Submodule.span Ω (S : Set E) = ⊤) :
    ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k))
      (z : (Σ k, ι' k) → Ω),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧
      ∀ j c, mseg (joinCoord x z) c ≠ 0 →
        LocFree (chartRing O (mseg (joinCoord x z)) c) (Module.finrank Ω E)
          (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set E)) ∧
        Summand (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set E)) (U j) := by
  classical
  let W : Bool × I → Submodule Ω E := fun q => if q.1 then U q.2 else ⊥
  obtain ⟨K', i1, i2, ι', i3, z, hz, hfree⟩ := PositivityTheory.Xgn.t_flatten_many O Ω K ι x d hm hf (Bool × I)
    (fun q => Module.finrank Ω (E ⧸ W q)) (fun q => E ⧸ W q)
    (fun q c => (Γ q.2 c).map (W q).mkQ.toAddMonoidHom) (fun q => ⟨rfl, fam_map O x (hΓ q.2).1 _, by
      intro c hc
      obtain ⟨S, hS, hT⟩ := (hΓ q.2).2 c hc
      refine ⟨S.image (W q).mkQ, ?_, ?_⟩
      · rw [hS, map_span, Finset.coe_image]
      · rw [Finset.coe_image, ← Submodule.map_span, hT, Submodule.map_top, Submodule.range_mkQ]⟩)
  refine ⟨K', i1, i2, ι', i3, z, hz, fun j c hc => ?_⟩
  have key : ∀ q : Bool × I, LocFree (chartRing O (mseg (joinCoord x z)) c) (Module.finrank Ω (E ⧸ W q))
      ((spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ q.2 (restrictChart c) : Set E)).map
        (W q).mkQ.toAddMonoidHom) := by
    intro q
    rw [map_span]
    exact hfree q c hc
  have h0 := locFree_of_bot _ (span_stable _ _) (key (false, j))
  have h1 := h0
  rw [← (PositivityTheory.Xgn.A_summand_of_quot.exists_dual _ h0).1] at h1
  exact ⟨h1, (PositivityTheory.Xgn.summand_iff_locFree_quot _ (U j) _ _ _ h1).1 (key (true, j))⟩

/- English proof (translation)
Establish `: ∀ v, bcMap Ω Ω J v = v` using `fun v => rfl`. Simplify using `[this]`.
-/
theorem bc_image {Ω : Type} [Field Ω] (J : Type) (S : Set (J → Ω)) : bcMap Ω Ω J '' S = S := by
  have : ∀ v, bcMap Ω Ω J v = v := fun v => rfl
  simp [this]

/- English proof (translation)
Unfold `vanSub`. Use `congr 1`. Use extensionality with `y`. Use `forall_congr' fun j => imp_congr_left ?_` and prove the remaining obligations. Use `j.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem vanSub_min (Ω F : Type) [Field Ω] [Zero F] (n i : ℕ) :
    vanSub Ω F n (min i n) = vanSub Ω F n i := by
  unfold vanSub
  congr 1
  ext y
  refine forall_congr' fun j => imp_congr_left ?_
  have := j.2
  omega

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x d hm hf F _ _ _ n Sg _ r s p _ w χ φ D hD`. Set `E` to `(Fin n → F) → Ω`. Set `T : Set E` to `Set.range fun j : Fin n → F => (Pi.single j (p : Ω) : E)`. Establish `hl1 : ∀ (R : Subalgebra O Ω) (D' : LieLatticeData Ω F n Sg r s), D'.l1 R p = D'.M ⊔ spanOver R T`. Introduce `R D'`.

Rewrite using `[LieLatticeData.l1, mulLat_std]`. Introduce the local definition `U : Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n) → Submodule Ω E`. Consider the case `none => ⊥`. Consider the case `some (.inl τ) => LinearMap.range (linMap n fun a => algebraMap O Ω (χ τ a))`. Consider the case `some (.inr (.inl i)) => vanSub Ω F n i`.

Consider the case `some (.inr (.inr q)) => charSub (fun a => algebraMap O Ω (χ q.1 a)) q.2`. Introduce the local definition `Γ : Bool → (∀ k, ι k) → AddSubgroup E`. Consider the case `true => fun c => (D c).M ⊔ spanOver (chartRing O (mseg x) c) T`. Consider the case `false => fun c => (D c).M`. Take `⟨K', i1, i2, ι', i3, z, hz, hfree⟩` from `flatten_summand O Ω K ι x d hm hf (Bool × Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n)) E (fun q => U q.2) (fun q => Γ q.1) (by`.

Introduce and unpack `⟨b, j⟩`. Consider the cases of `b`. Conclude with `⟨hD.famM, fun c hc => fg_of_locFree _ (hD.base c hc).freeM⟩`. Use `⟨fam_sup O x hD.famM (fam_span O x T), fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hT⟩` from `fg_of_locFree _ (hD.base c hc).freeM`.

Use `⟨S ∪ Finset.univ.image fun j : Fin n → F => (Pi.single j (p : Ω) : E), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_union, span_union, ← hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Rewrite using `[Finset.coe_union, Submodule.span_union, hT, top_sup_eq])`. Use `⟨K', i1, i2, ι', i3, z, hz, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨hc0, hle⟩` from `((PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 K' ι' z).2 c hc`.

Establish `hM : (pullFamily O x z D c).M = spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ false (restrictChart c) : Set E)` using `by show spanOver _ (bcMap Ω Ω _ '' _) = _`. Rewrite using `[bc_image]`. Establish `hL : (pullFamily O x z D c).l1 (chartRing O (mseg (joinCoord x z)) c) p = spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ true (restrictChart c) : Set E)`. Rewrite using `[hl1, hM, ← span_union]`. Establish `hst` using `(hD.base _ hc0).freeM.1`.

Establish `: Γ true (restrictChart c) = spanOver (chartRing O (mseg x) (restrictChart c)) (((D (restrictChart c)).M : Set E) ∪ T)`. Rewrite using `[span_union, span_self _ hst]`. Rewrite using `[this, span_span _ hle]`. Establish `hr : Module.finrank Ω E = Fintype.card F ^ n` using `by simp [E]`. Use `⟨?_, fun τ => ?_, fun i => ?_, fun τ i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hL, ← hr]`. Conclude with `(hfree (true, none) c hc).1`. Rewrite using `[hL]`. Conclude with `(hfree (true, some (.inl τ)) c hc).2`. Rewrite using `[hM, ← vanSub_min]`.

Conclude with `(hfree (false, some (.inr (.inl ⟨min i n, by omega⟩))) c hc).2`. Rewrite using `[hM]`. Conclude with `(hfree (false, some (.inr (.inr (τ, i)))) c hc).2`.
-/
theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hm hf F _ _ _ n Sg _ r s p _ w χ φ D hD
  let E := (Fin n → F) → Ω
  let T : Set E := Set.range fun j : Fin n → F => (Pi.single j (p : Ω) : E)
  have hl1 : ∀ (R : Subalgebra O Ω) (D' : LieLatticeData Ω F n Sg r s), D'.l1 R p = D'.M ⊔ spanOver R T := by
    intro R D'
    rw [LieLatticeData.l1, mulLat_std]
  let U : Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n) → Submodule Ω E
    | none => ⊥
    | some (.inl τ) => LinearMap.range (linMap n fun a => algebraMap O Ω (χ τ a))
    | some (.inr (.inl i)) => vanSub Ω F n i
    | some (.inr (.inr q)) => charSub (fun a => algebraMap O Ω (χ q.1 a)) q.2
  let Γ : Bool → (∀ k, ι k) → AddSubgroup E
    | true => fun c => (D c).M ⊔ spanOver (chartRing O (mseg x) c) T
    | false => fun c => (D c).M
  obtain ⟨K', i1, i2, ι', i3, z, hz, hfree⟩ := flatten_summand O Ω K ι x d hm hf
    (Bool × Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n)) E (fun q => U q.2) (fun q => Γ q.1) (by
      rintro ⟨b, j⟩
      cases b
      · exact ⟨hD.famM, fun c hc => fg_of_locFree _ (hD.base c hc).freeM⟩
      · refine ⟨fam_sup O x hD.famM (fam_span O x T), fun c hc => ?_⟩
        obtain ⟨S, hS, hT⟩ := fg_of_locFree _ (hD.base c hc).freeM
        refine ⟨S ∪ Finset.univ.image fun j : Fin n → F => (Pi.single j (p : Ω) : E), ?_, ?_⟩
        · rw [Finset.coe_union, span_union, ← hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]
        · rw [Finset.coe_union, Submodule.span_union, hT, top_sup_eq])
  refine ⟨K', i1, i2, ι', i3, z, hz, fun c hc => ?_⟩
  obtain ⟨hc0, hle⟩ := ((PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 K' ι' z).2 c hc
  have hM : (pullFamily O x z D c).M =
      spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ false (restrictChart c) : Set E) := by
    show spanOver _ (bcMap Ω Ω _ '' _) = _
    rw [bc_image]
  have hL : (pullFamily O x z D c).l1 (chartRing O (mseg (joinCoord x z)) c) p =
      spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ true (restrictChart c) : Set E) := by
    rw [hl1, hM, ← span_union]
    have hst := (hD.base _ hc0).freeM.1
    have : Γ true (restrictChart c) =
        spanOver (chartRing O (mseg x) (restrictChart c)) (((D (restrictChart c)).M : Set E) ∪ T) := by
      rw [span_union, span_self _ hst]
    rw [this, span_span _ hle]
  have hr : Module.finrank Ω E = Fintype.card F ^ n := by simp [E]
  refine ⟨?_, fun τ => ?_, fun i => ?_, fun τ i => ?_⟩
  · rw [hL, ← hr]
    exact (hfree (true, none) c hc).1
  · rw [hL]
    exact (hfree (true, some (.inl τ)) c hc).2
  · rw [hM, ← vanSub_min]
    exact (hfree (false, some (.inr (.inl ⟨min i n, by omega⟩))) c hc).2
  · rw [hM]
    exact (hfree (false, some (.inr (.inr (τ, i)))) c hc).2

end GlobalTheory.CompanionTheory.Ar.FamGood1
