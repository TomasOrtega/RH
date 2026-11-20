import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.T.LocStepPf

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

/- English proof (translation)
Use `continuous_pi fun ij => ?_` and prove the remaining obligations. Use `show Continuous fun x : Matrix (Fin n) (Fin n) k => trace (((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k) * x ^ (ij.1 : ℕ))`. Conclude with `(continuous_const.matrix_mul (continuous_pow _)).matrix_trace`.
-/
theorem continuous_pZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    Continuous (pZ Z : Matrix (Fin n) (Fin n) k → _) := by
  refine continuous_pi fun ij => ?_
  show Continuous fun x : Matrix (Fin n) (Fin n) k =>
    trace (((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k) * x ^ (ij.1 : ℕ))
  exact (continuous_const.matrix_mul (continuous_pow _)).matrix_trace

/- English proof (translation)
Establish `: Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a}`. Use extensionality with `x`. Simplify using `[Bz]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)`.
-/
theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Bz Z) := by
  have : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a} := by
    ext x
    simp [Bz]
  rw [this]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use function extensionality and compare the values at `ij`. Simplify using `only [pZ]`. Establish `hb` using `hg _ ((Module.finBasis k Z) ij.2).2`. Rewrite using `[Units.conj_pow]`. Use `set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z) ij.2 : Matrix (Fin n) (Fin n) k)`.

Use `set y := x ^ (ij.1 : ℕ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = ((g.val * b) * y * g⁻¹.val).trace := by rw [hb]`. Use `_ = (g⁻¹.val * (g.val * b * y)).trace := Matrix.trace_mul_comm _ _`.

Use `_ = (b * y).trace := by`. Rewrite using `[← mul_assoc, ← mul_assoc]`. Simplify using the standard rewrite rules.
-/
theorem pZ_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : pZ Z (g.val * x * g⁻¹.val) = pZ Z x := by
  funext ij
  simp only [pZ]
  have hb := hg _ ((Module.finBasis k Z) ij.2).2
  rw [Units.conj_pow]
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z) ij.2 : Matrix (Fin n) (Fin n) k)
  set y := x ^ (ij.1 : ℕ)
  calc (b * (g.val * y * g⁻¹.val)).trace = ((b * g.val) * y * g⁻¹.val).trace := by
        simp only [mul_assoc]
    _ = ((g.val * b) * y * g⁻¹.val).trace := by rw [hb]
    _ = (g⁻¹.val * (g.val * b * y)).trace := Matrix.trace_mul_comm _ _
    _ = (b * y).trace := by
        rw [← mul_assoc, ← mul_assoc]
        simp

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_iff_lemma {X : Type} [TopologicalSpace X] (U : Set X) (F : X → ℂ) :
    F ∈ supportedIn U ↔ (IsLocallyConstant F ∧ HasCompactSupport F) ∧ Function.support F ⊆ U :=
  Iff.rfl

/- English proof (translation)
Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ s`. Conclude with `⟨s, hs.isOpen, hx, fun y hy => by simp [Set.indicator_apply, hx, hy]⟩`. Use `⟨sᶜ, hs.isClosed.isOpen_compl, hx, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : y ∉ s` using `hy`.

Simplify using `[Set.indicator_apply, hx, hy']`.
-/
private theorem isLocallyConstant_indicator_one_of_isClopen {X : Type} [TopologicalSpace X] {s : Set X} (hs : IsClopen s) :
    IsLocallyConstant (s.indicator (1 : X → ℂ)) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ s
  · exact ⟨s, hs.isOpen, hx, fun y hy => by simp [Set.indicator_apply, hx, hy]⟩
  · refine ⟨sᶜ, hs.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    have hy' : y ∉ s := hy
    simp [Set.indicator_apply, hx, hy']

/- English proof (translation)
Rewrite `hF`, the goal using `[mem_iff_lemma]`. Take `⟨⟨hlc, hcs⟩, hsub⟩` from `hF`. Conclude with `⟨⟨hlc.mul (isLocallyConstant_indicator_one_of_isClopen hs), hcs.mul_right⟩, (Function.support_mul_subset_left _ _).trans hsub⟩`.
-/
private theorem mul_indicator_mem_supportedIn_of_isClopen {X : Type} [TopologicalSpace X] {U s : Set X} (hs : IsClopen s)
    {F : X → ℂ} (hF : F ∈ supportedIn U) : F * s.indicator 1 ∈ supportedIn U := by
  rw [mem_iff_lemma] at hF ⊢
  obtain ⟨⟨hlc, hcs⟩, hsub⟩ := hF
  exact ⟨⟨hlc.mul (isLocallyConstant_indicator_one_of_isClopen hs), hcs.mul_right⟩, (Function.support_mul_subset_left _ _).trans hsub⟩

/- English proof (translation)
Unfold `LocStep Kills`. Introduce `m Z hCR ξ hsupp hinv hfib f hf`. Use `haveI : NonarchimedeanRing k := by convert! (ValuativeRel.nonarchimedeanRing k)`. Conclude with `Valuation.toTopologicalSpace_eq _`. Establish `hbasis : TopologicalSpace.IsTopologicalBasis {s : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k) | IsClopen s}` using `loc_compact_Haus_tot_disc_of_zero_dim`.

Take `⟨q, hq_def⟩ : ∃ q : Sp k m → (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), q = fun p => pZ Z p.1` from `⟨_, rfl⟩`. Establish `hq : Continuous q` using `by rw [hq_def]; exact (continuous_pZ Z).comp continuous_fst`. Take `⟨⟨hflc, hfcs⟩, hfsub⟩` from `(mem_iff_lemma _ _).1 hf`. Establish `hfS : f ∈ supportedIn (univ : Set (Sp k m))` using `(mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, subset_univ _⟩`. Establish `hloc : ∀ y, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsOpen O ∧ y ∈ O ∧ ∀ W, IsClopen W → W ⊆ O → ξ (f * (q ⁻¹' W).indicator 1) = 0`.

Introduce `y`. Take `⟨A, hA⟩ : ∃ A : Set (Sp k m → ℂ), A = {F | (∃ g ∈ Gz Z, ∃ h ∈ supportedIn (univ : Set (Sp k m)), F = h - fun p => h (act g p)) ∨ (F ∈ supportedIn (univ : Set (Sp k m)) ∧ ∀ p ∈ (Bz Z ∩ pZ Z ⁻¹' {y}) ×ˢ (univ : Set (Fin m → k)), F p = 0)}` from `⟨_, rfl⟩`. Establish `hfJ : f ∈ Submodule.span ℂ A`. Break down `hfib y with ⟨c, hcZ, hc⟩ | hB` into its components or cases. Use `Submodule.subset_span ?_` and prove the remaining obligations.

Rewrite using `[hA, Set.mem_setOf_eq]`. Use `Or.inr ⟨hfS, fun p hp => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hpU` using `hfsub (Function.mem_support.mpr hne)`. Establish `hZN : p.1 ∈ ZN Z`.

Simplify using `only [ZN, Set.mem_setOf_eq]`. Conclude with `⟨c, hcZ, hc p.1 hp.1.1 hp.1.2⟩`. Conclude with `(show p.1 ∉ ZN Z from hpU.2) hZN`. Assume the negation of the conclusion as `hnot`. Take `⟨l, hlf, hlJ⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance`.

Establish `hz : ∀ F ∈ Submodule.span ℂ A, l F = 0`. Introduce `F hF`. Establish `h1` using `Submodule.mem_map_of_mem (f := l) hF`. Rewrite `h1` using `[hlJ]`. Conclude with `(Submodule.mem_bot ℂ).1 h1`.

Apply `hlf` to reduce the goal to its premises. Use `hB l ?_ ?_ f ((mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, fun p hp => (hfsub hp).1⟩)` and prove the remaining obligations. Introduce `F hF hvan`. Conclude with `hz F (Submodule.subset_span (by rw [hA, Set.mem_setOf_eq]; exact Or.inr ⟨hF, hvan⟩))`. Introduce `g hg F hF`.

Establish `h1` using `hz _ (Submodule.subset_span (by rw [hA, Set.mem_setOf_eq]; exact Or.inl ⟨g, hg, F, hF, rfl⟩))`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Conclude with `h1.symm`. Establish `hP : ∀ F ∈ Submodule.span ℂ A, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsOpen O ∧ y ∈ O ∧ ∀ W, IsClopen W → W ⊆ O → ξ (F * (q ⁻¹' W).indicator 1) = 0`. Introduce `F hF`.

Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Rewrite `hF` using `[hA, Set.mem_setOf_eq]`. Break down `hF with ⟨g, hg, h, hh, rfl⟩ | ⟨hrS, hvan⟩` into its components or cases. Use `⟨univ, isOpen_univ, mem_univ _, fun W hW _ => ?_⟩` and prove the remaining obligations.

Establish `hqa : ∀ p, q (act g p) = q p`. Introduce `p`. Rewrite using `[hq_def]`. Conclude with `pZ_conj Z hg p.1`. Use `set φ : Sp k m → ℂ := (q ⁻¹' W).indicator 1 with hφ`.

Establish `hφa : ∀ p, φ (act g p) = φ p`. Introduce `p`. Simplify using `only [hφ, Set.indicator_apply, Set.mem_preimage, hqa, Pi.one_apply]`. Establish `hsplit : (h - fun p => h (act g p)) * φ = h * φ - fun p => (h * φ) (act g p)`. Use function extensionality and compare the values at `p`.

Simplify using `only [Pi.mul_apply, Pi.sub_apply, hφa]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, map_sub, hinv g hg _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hh), sub_self]`. Take `⟨⟨hrlc, hrcs⟩, -⟩` from `(mem_iff_lemma _ _).1 hrS`. Establish `hsuppc : IsClosed (Function.support F)`.

Establish `h1` using `(hrlc.isOpen_fiber 0).isClosed_compl`. Establish `h2 : Function.support F = {x | F x = 0}ᶜ` using `by ext x; simp`. Rewrite using `[h2]`. Conclude with `h1`. Establish `hKc : IsCompact (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k))))` using `IsCompact.of_isClosed_subset hrcs (hsuppc.inter ((isClosed_Bz Z).prod isClosed_univ)) (inter_subset_left.trans (subset_tsupport F))`.

Establish `hKq` using `(hKc.image hq).isClosed`. Use `⟨(q '' (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k)))))ᶜ, hKq.isOpen_compl, ?_, fun W hW hWO => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨p, ⟨hpF, hpB⟩, hpy⟩`. Use `(Function.mem_support.mp hpF) (hvan p ⟨⟨hpB.1, ?_⟩, mem_univ _⟩)` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, Set.mem_singleton_iff, ← hpy, hq_def]`.

Use `hsupp _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hrS) (fun p hp => ?_)` and prove the remaining obligations. Distinguish the cases in `hpW : q p ∈ W`. Establish `h0 : F p = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hWO hpW ⟨p, ⟨hne, hp⟩, rfl⟩`.

Simplify using `[h0]`. Simplify using `[Set.indicator_apply, hpW]`. Consider the case `zero => exact ⟨univ, isOpen_univ, mem_univ _, fun W _ _ => by simp⟩`. Consider the case `add F F' _ _ hF hF'`. Take `⟨O, hO, hyO, hOW⟩` from `hF`.

Take `⟨O', hO', hyO', hOW'⟩` from `hF'`. Conclude with `⟨O ∩ O', hO.inter hO', ⟨hyO, hyO'⟩, fun W hW hWO => by`. Rewrite using `[add_mul, map_add, hOW W hW (hWO.trans inter_subset_left), hOW' W hW (hWO.trans inter_subset_right), add_zero]⟩`. Consider the case `smul a F _ hF`. Take `⟨O, hO, hyO, hOW⟩` from `hF`.

Conclude with `⟨O, hO, hyO, fun W hW hWO => by rw [smul_mul_assoc, map_smul, hOW W hW hWO, smul_zero]⟩`. Conclude with `hP f hfJ`. Use `choose O hO hyO hOW using hloc`. Establish `hV : ∀ y, ∃ V : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsClopen V ∧ y ∈ V ∧ V ⊆ O y` using `fun y => by`. Take `⟨V, hVB, hyV, hVO⟩` from `hbasis.exists_subset_of_mem_open (hyO y) (hO y)`.

Conclude with `⟨V, hVB, hyV, hVO⟩`. Use `choose V hVc hyV hVO using hV`. Establish `hunion : ∀ B1 B2 : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsClopen B1 → (∀ W, IsClopen W → W ⊆ B1 → ξ (f * (q ⁻¹' W).indicator 1) = 0) → (∀ W, IsClopen W → W ⊆ B2 → ξ (f * (q ⁻¹' W).indicator 1) = 0) → ∀ W, IsClopen W → W ⊆ B1 ∪ B2 → ξ (f * (q ⁻¹' W).indicator 1) = …`. Introduce `B1 B2 hB1 hQ1 hQ2 W hW hWB`. Establish `hsplit : f * (q ⁻¹' W).indicator 1 = f * (q ⁻¹' (W ∩ B1)).indicator 1 + f * (q ⁻¹' (W \ B1)).indicator 1`.

Use function extensionality and compare the values at `p`. Apply the tactic sequence `by_cases h1 : q p ∈ W <;> by_cases h2 : q p ∈ B1 <;> simp [Set.indicator_apply, h1, h2]`. Rewrite using `[hsplit, map_add, hQ1 _ (hW.inter hB1) inter_subset_right, hQ2 _ (hW.diff hB1) (fun z hz => (hWB hz.1).resolve_left hz.2), add_zero]`. Establish `hfin : ∀ t : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsClopen (⋃ i ∈ t, V i) ∧ ∀ W, IsClopen W → W ⊆ ⋃ i ∈ t, V i → ξ (f * (q ⁻¹' W).indicator 1) = 0`. Introduce `t`.

Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Establish `he : (⋃ i ∈ (∅ : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k)), V i) = ∅`. Use extensionality with `z`. Simplify using the standard rewrite rules.

Rewrite using `[he]`. Use `⟨isClopen_empty, fun W _ hW => ?_⟩` and prove the remaining obligations. Establish `hW0 : W = ∅` using `Set.subset_empty_iff.mp hW`. Substitute `hW0` using the available equality. Establish `h0 : f * (q ⁻¹' (∅ : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k))).indicator 1 = 0`.

Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Rewrite using `[h0, map_zero]`. Consider the case `insert a s _ ih`. Rewrite using `[Finset.set_biUnion_insert]`.

Conclude with `⟨(hVc a).union ih.1, hunion _ _ (hVc a) (fun W hW hWV => hOW a W hW (hWV.trans (hVO a))) ih.2⟩`. Take `⟨t, ht⟩` from `(IsCompact.image hfcs hq).elim_finite_subcover V (fun y => (hVc y).isOpen) (fun z _ => mem_iUnion.2 ⟨z, hyV z⟩)`. Take `⟨hc, hQt⟩` from `hfin t`. Establish `heq : f * (q ⁻¹' (⋃ i ∈ t, V i)).indicator 1 = f`. Use function extensionality and compare the values at `p`.

Distinguish the cases in `hp : f p = 0`. Simplify using `[hp]`. Establish `hmem : q p ∈ ⋃ i ∈ t, V i` using `ht ⟨p, subset_tsupport f (Function.mem_support.mpr hp), rfl⟩`. Rewrite using `[Pi.mul_apply, Set.indicator_of_mem (show p ∈ q ⁻¹' (⋃ i ∈ t, V i) from hmem), Pi.one_apply, mul_one]`. Rewrite using `[← heq]`.

Conclude with `hQt _ hc subset_rfl`.
-/
theorem local_descent_holds : LocStep (k := k) := by
  classical
  unfold LocStep Kills
  intro m Z hCR ξ hsupp hinv hfib f hf
  haveI : NonarchimedeanRing k := by
    convert! (ValuativeRel.nonarchimedeanRing k)
    exact Valuation.toTopologicalSpace_eq _
  have hbasis : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  obtain ⟨q, hq_def⟩ : ∃ q : Sp k m → (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      q = fun p => pZ Z p.1 := ⟨_, rfl⟩
  have hq : Continuous q := by rw [hq_def]; exact (continuous_pZ Z).comp continuous_fst
  obtain ⟨⟨hflc, hfcs⟩, hfsub⟩ := (mem_iff_lemma _ _).1 hf
  have hfS : f ∈ supportedIn (univ : Set (Sp k m)) :=
    (mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, subset_univ _⟩
  have hloc : ∀ y, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsOpen O ∧ y ∈ O ∧
      ∀ W, IsClopen W → W ⊆ O → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro y
    obtain ⟨A, hA⟩ : ∃ A : Set (Sp k m → ℂ), A = {F | (∃ g ∈ Gz Z, ∃ h ∈ supportedIn (univ : Set (Sp k m)),
        F = h - fun p => h (act g p)) ∨ (F ∈ supportedIn (univ : Set (Sp k m)) ∧
        ∀ p ∈ (Bz Z ∩ pZ Z ⁻¹' {y}) ×ˢ (univ : Set (Fin m → k)), F p = 0)} := ⟨_, rfl⟩
    have hfJ : f ∈ Submodule.span ℂ A := by
      rcases hfib y with ⟨c, hcZ, hc⟩ | hB
      · refine Submodule.subset_span ?_
        rw [hA, Set.mem_setOf_eq]
        refine Or.inr ⟨hfS, fun p hp => ?_⟩
        by_contra hne
        have hpU := hfsub (Function.mem_support.mpr hne)
        have hZN : p.1 ∈ ZN Z := by
          simp only [ZN, Set.mem_setOf_eq]
          exact ⟨c, hcZ, hc p.1 hp.1.1 hp.1.2⟩
        exact (show p.1 ∉ ZN Z from hpU.2) hZN
      · by_contra hnot
        obtain ⟨l, hlf, hlJ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
        have hz : ∀ F ∈ Submodule.span ℂ A, l F = 0 := by
          intro F hF
          have h1 := Submodule.mem_map_of_mem (f := l) hF
          rw [hlJ] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        apply hlf
        refine hB l ?_ ?_ f ((mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, fun p hp => (hfsub hp).1⟩)
        · intro F hF hvan
          exact hz F (Submodule.subset_span (by rw [hA, Set.mem_setOf_eq]; exact Or.inr ⟨hF, hvan⟩))
        · intro g hg F hF
          have h1 := hz _ (Submodule.subset_span
            (by rw [hA, Set.mem_setOf_eq]; exact Or.inl ⟨g, hg, F, hF, rfl⟩))
          rw [map_sub, sub_eq_zero] at h1
          exact h1.symm
    have hP : ∀ F ∈ Submodule.span ℂ A, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
        IsOpen O ∧ y ∈ O ∧ ∀ W, IsClopen W → W ⊆ O → ξ (F * (q ⁻¹' W).indicator 1) = 0 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        rw [hA, Set.mem_setOf_eq] at hF
        rcases hF with ⟨g, hg, h, hh, rfl⟩ | ⟨hrS, hvan⟩
        · refine ⟨univ, isOpen_univ, mem_univ _, fun W hW _ => ?_⟩
          have hqa : ∀ p, q (act g p) = q p := by
            intro p; rw [hq_def]; exact pZ_conj Z hg p.1
          set φ : Sp k m → ℂ := (q ⁻¹' W).indicator 1 with hφ
          have hφa : ∀ p, φ (act g p) = φ p := by
            intro p; simp only [hφ, Set.indicator_apply, Set.mem_preimage, hqa, Pi.one_apply]
          have hsplit : (h - fun p => h (act g p)) * φ = h * φ - fun p => (h * φ) (act g p) := by
            funext p
            simp only [Pi.mul_apply, Pi.sub_apply, hφa]
            ring
          rw [hsplit, map_sub, hinv g hg _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hh), sub_self]
        · obtain ⟨⟨hrlc, hrcs⟩, -⟩ := (mem_iff_lemma _ _).1 hrS
          have hsuppc : IsClosed (Function.support F) := by
            have h1 := (hrlc.isOpen_fiber 0).isClosed_compl
            have h2 : Function.support F = {x | F x = 0}ᶜ := by ext x; simp
            rw [h2]; exact h1
          have hKc : IsCompact (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k)))) :=
            IsCompact.of_isClosed_subset hrcs (hsuppc.inter ((isClosed_Bz Z).prod isClosed_univ))
              (inter_subset_left.trans (subset_tsupport F))
          have hKq := (hKc.image hq).isClosed
          refine ⟨(q '' (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k)))))ᶜ,
            hKq.isOpen_compl, ?_, fun W hW hWO => ?_⟩
          · rintro ⟨p, ⟨hpF, hpB⟩, hpy⟩
            refine (Function.mem_support.mp hpF) (hvan p ⟨⟨hpB.1, ?_⟩, mem_univ _⟩)
            rw [Set.mem_preimage, Set.mem_singleton_iff, ← hpy, hq_def]
          · refine hsupp _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hrS) (fun p hp => ?_)
            by_cases hpW : q p ∈ W
            · have h0 : F p = 0 := by
                by_contra hne
                exact hWO hpW ⟨p, ⟨hne, hp⟩, rfl⟩
              simp [h0]
            · simp [Set.indicator_apply, hpW]
      | zero => exact ⟨univ, isOpen_univ, mem_univ _, fun W _ _ => by simp⟩
      | add F F' _ _ hF hF' =>
        obtain ⟨O, hO, hyO, hOW⟩ := hF
        obtain ⟨O', hO', hyO', hOW'⟩ := hF'
        exact ⟨O ∩ O', hO.inter hO', ⟨hyO, hyO'⟩, fun W hW hWO => by
          rw [add_mul, map_add, hOW W hW (hWO.trans inter_subset_left),
            hOW' W hW (hWO.trans inter_subset_right), add_zero]⟩
      | smul a F _ hF =>
        obtain ⟨O, hO, hyO, hOW⟩ := hF
        exact ⟨O, hO, hyO, fun W hW hWO => by rw [smul_mul_assoc, map_smul, hOW W hW hWO, smul_zero]⟩
    exact hP f hfJ
  choose O hO hyO hOW using hloc
  have hV : ∀ y, ∃ V : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      IsClopen V ∧ y ∈ V ∧ V ⊆ O y := fun y => by
    obtain ⟨V, hVB, hyV, hVO⟩ := hbasis.exists_subset_of_mem_open (hyO y) (hO y)
    exact ⟨V, hVB, hyV, hVO⟩
  choose V hVc hyV hVO using hV
  have hunion : ∀ B1 B2 : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsClopen B1 →
      (∀ W, IsClopen W → W ⊆ B1 → ξ (f * (q ⁻¹' W).indicator 1) = 0) →
      (∀ W, IsClopen W → W ⊆ B2 → ξ (f * (q ⁻¹' W).indicator 1) = 0) →
      ∀ W, IsClopen W → W ⊆ B1 ∪ B2 → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro B1 B2 hB1 hQ1 hQ2 W hW hWB
    have hsplit : f * (q ⁻¹' W).indicator 1 =
        f * (q ⁻¹' (W ∩ B1)).indicator 1 + f * (q ⁻¹' (W \ B1)).indicator 1 := by
      funext p
      by_cases h1 : q p ∈ W <;> by_cases h2 : q p ∈ B1 <;> simp [Set.indicator_apply, h1, h2]
    rw [hsplit, map_add, hQ1 _ (hW.inter hB1) inter_subset_right,
      hQ2 _ (hW.diff hB1) (fun z hz => (hWB hz.1).resolve_left hz.2), add_zero]
  have hfin : ∀ t : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      IsClopen (⋃ i ∈ t, V i) ∧
      ∀ W, IsClopen W → W ⊆ ⋃ i ∈ t, V i → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have he : (⋃ i ∈ (∅ : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k)), V i) = ∅ := by
        ext z; simp
      rw [he]
      refine ⟨isClopen_empty, fun W _ hW => ?_⟩
      have hW0 : W = ∅ := Set.subset_empty_iff.mp hW
      subst hW0
      have h0 : f * (q ⁻¹' (∅ : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k))).indicator 1 = 0 := by
        funext p; simp
      rw [h0, map_zero]
    | insert a s _ ih =>
      rw [Finset.set_biUnion_insert]
      exact ⟨(hVc a).union ih.1, hunion _ _ (hVc a)
        (fun W hW hWV => hOW a W hW (hWV.trans (hVO a))) ih.2⟩
  obtain ⟨t, ht⟩ := (IsCompact.image hfcs hq).elim_finite_subcover V (fun y => (hVc y).isOpen)
    (fun z _ => mem_iUnion.2 ⟨z, hyV z⟩)
  obtain ⟨hc, hQt⟩ := hfin t
  have heq : f * (q ⁻¹' (⋃ i ∈ t, V i)).indicator 1 = f := by
    funext p
    by_cases hp : f p = 0
    · simp [hp]
    · have hmem : q p ∈ ⋃ i ∈ t, V i := ht ⟨p, subset_tsupport f (Function.mem_support.mpr hp), rfl⟩
      rw [Pi.mul_apply, Set.indicator_of_mem (show p ∈ q ⁻¹' (⋃ i ∈ t, V i) from hmem),
        Pi.one_apply, mul_one]
  rw [← heq]
  exact hQt _ hc subset_rfl

end PositivityTheory.RgUd.T.LocStepPf
