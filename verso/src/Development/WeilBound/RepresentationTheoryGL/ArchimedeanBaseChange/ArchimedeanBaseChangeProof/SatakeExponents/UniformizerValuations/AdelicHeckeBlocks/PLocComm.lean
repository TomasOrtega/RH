import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

namespace LocComm

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Simplify using `[hint]`.
-/
theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [mconv, Pi.zero_apply, mul_zero]`. Conclude with `hint_zero _`.
-/
theorem mconv_zero_right {a b : ℕ} {w : Pl E} (u : LF a b w) : mconv u (0 : LF a b w) = 0 := by
  funext m
  simp only [mconv, Pi.zero_apply, mul_zero]
  exact hint_zero _

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [mconv, Pi.zero_apply, zero_mul]`. Conclude with `hint_zero _`.
-/
theorem mconv_zero_left {a b : ℕ} {w : Pl E} (u : LF a b w) : mconv (0 : LF a b w) u = 0 := by
  funext m
  simp only [mconv, Pi.zero_apply, zero_mul]
  exact hint_zero _

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[lfStar]`.
-/
theorem lfStar_zero {a b : ℕ} {w : Pl E} : lfStar (0 : LF a b w) = 0 := by
  funext y
  simp [lfStar]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ L`. Establish `hy' : y⁻¹ ∈ L` using `L.inv_mem hy`. Simplify using `only [lfStar, idem, Set.indicator_of_mem (show y⁻¹ ∈ (L : Set _) from hy'), Set.indicator_of_mem (show y ∈ (L : Set _) from hy)]`. Conclude with `Complex.conj_natCast _`.

Establish `hy' : y⁻¹ ∉ L` using `fun h => hy (by simpa using L.inv_mem h)`. Simplify using `only [lfStar, idem, Set.indicator_of_notMem (show y⁻¹ ∉ (L : Set _) from hy'), Set.indicator_of_notMem (show y ∉ (L : Set _) from hy), map_zero]`.
-/
theorem lfStar_idem {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : lfStar (idem L) = idem L := by
  funext y
  by_cases hy : y ∈ L
  · have hy' : y⁻¹ ∈ L := L.inv_mem hy
    simp only [lfStar, idem, Set.indicator_of_mem (show y⁻¹ ∈ (L : Set _) from hy'),
      Set.indicator_of_mem (show y ∈ (L : Set _) from hy)]
    exact Complex.conj_natCast _
  · have hy' : y⁻¹ ∉ L := fun h => hy (by simpa using L.inv_mem h)
    simp only [lfStar, idem, Set.indicator_of_notMem (show y⁻¹ ∉ (L : Set _) from hy'),
      Set.indicator_of_notMem (show y ∉ (L : Set _) from hy), map_zero]

section Hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩`.
-/
theorem isHecke_zero {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHecke K (0 : G → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `isHecke_zero K`. Consider the case `insert i s hi ih`.

Establish `h1` using `h i (Finset.mem_insert_self _ _)`. Establish `h2` using `ih fun j hj => h j (Finset.mem_insert_of_mem hj)`. Use `⟨?_, fun k hk x => ?_⟩` and prove the remaining obligations. Establish `e : (fun y => ∑ j ∈ insert i s, c j * g j y) = (fun _ => c i) * g i + fun y => ∑ j ∈ s, c j * g j y`. Use function extensionality and compare the values at `y`.

Simplify using `[Finset.sum_insert hi]`. Rewrite using `[e]`. Conclude with `(h1.1.mul_left).add h2.1`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp only [Finset.sum_insert hi, (h1.2 k hk x).1, (h1.2 k hk x).2, (h2.2 k hk x).1, (h2.2 k hk x).2]`.
-/
theorem isHecke_sum {G ι : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (s : Finset ι) (c : ι → ℂ)
    (g : ι → G → ℂ) (h : ∀ i ∈ s, IsHecke K (g i)) : IsHecke K (fun y => ∑ i ∈ s, c i * g i y) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isHecke_zero K
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨?_, fun k hk x => ?_⟩
    · have e : (fun y => ∑ j ∈ insert i s, c j * g j y) = (fun _ => c i) * g i + fun y => ∑ j ∈ s, c j * g j y := by
        funext y
        simp [Finset.sum_insert hi]
      rw [e]
      exact (h1.1.mul_left).add h2.1
    · refine ⟨?_, ?_⟩ <;> simp only [Finset.sum_insert hi, (h1.2 k hk x).1, (h1.2 k hk x).2, (h2.2 k hk x).1, (h2.2 k hk x).2]

variable {m : ℕ} {w : Pl E}

/- English proof (translation)
Unfold `dcos`. Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, by`. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨k * x, mul_mem hk hx, z, hz, by rw [e]; group⟩`.
-/
theorem dcos_mul_left (t g k : GLw m w) (hk : k ∈ iwGL m w) : dcos m w t (k * g) = dcos m w t g := by
  unfold dcos
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, e⟩
    exact ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, by
      calc g = k⁻¹ * (k * g) := by group
        _ = _ := by rw [e]; group⟩
  · rintro ⟨x, hx, z, hz, e⟩
    exact ⟨k * x, mul_mem hk hx, z, hz, by rw [e]; group⟩

/- English proof (translation)
Unfold `dcos`. Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), by`. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨x, hx, z * k, mul_mem hz hk, by rw [e]; group⟩`.
-/
theorem dcos_mul_right (t g k : GLw m w) (hk : k ∈ iwGL m w) : dcos m w t (g * k) = dcos m w t g := by
  unfold dcos
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, e⟩
    exact ⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), by
      calc g = (g * k) * k⁻¹ := by group
        _ = _ := by rw [e]; group⟩
  · rintro ⟨x, hx, z, hz, e⟩
    exact ⟨x, hx, z * k, mul_mem hz hk, by rw [e]; group⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w m).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _)) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w m)`.
-/
theorem isCompact_iwGL : IsCompact (iwGL m w : Set (GLw m w)) :=
  (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w m).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _)) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w m)

/- English proof (translation)
Establish `hc : Continuous fun p : GLw m w × GLw m w => p.1 * t * p.2` using `(continuous_fst.mul continuous_const).mul continuous_snd`. Use `⟨(fun p : GLw m w × GLw m w => p.1 * t * p.2) '' ((iwGL m w : Set (GLw m w)) ×ˢ (iwGL m w : Set (GLw m w))), (isCompact_iwGL.prod isCompact_iwGL).image hc, fun g hg => ?_⟩` and prove the remaining obligations. Unfold `dcos`. Rewrite using `[if_neg]`. Introduce and unpack `⟨x, hx, z, hz, e⟩`.

Conclude with `hg ⟨(x, z), ⟨hx, hz⟩, e.symm⟩`.
-/
theorem dcos_supp (t : GLw m w) : ∃ C : Set (GLw m w), IsCompact C ∧ ∀ g ∉ C, dcos m w t g = 0 := by
  have hc : Continuous fun p : GLw m w × GLw m w => p.1 * t * p.2 :=
    (continuous_fst.mul continuous_const).mul continuous_snd
  refine ⟨(fun p : GLw m w × GLw m w => p.1 * t * p.2) '' ((iwGL m w : Set (GLw m w)) ×ˢ (iwGL m w : Set (GLw m w))),
    (isCompact_iwGL.prod isCompact_iwGL).image hc, fun g hg => ?_⟩
  unfold dcos
  rw [if_neg]
  rintro ⟨x, hx, z, hz, e⟩
  exact hg ⟨(x, z), ⟨hx, hz⟩, e.symm⟩

/- English proof (translation)
Take `⟨A, hA, hA0⟩` from `dcos_supp (m := a) (w := w) (tdiag ϖ x)`. Take `⟨B, hB, hB0⟩` from `dcos_supp (m := b) (w := w) (tdiag ϖ y)`. Use `⟨HasCompactSupport.intro (hA.prod hB) fun g hg => ?_, fun k hk g => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_prod, not_and_or] at hg`. Break down `hg with h | h` into its components or cases.

Simplify using `[dc2, hA0 _ h]`. Simplify using `[dc2, hB0 _ h]`. Take `⟨h1, h2⟩` from `Subgroup.mem_prod.1 hk`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp only [dc2, Prod.fst_mul, Prod.snd_mul, dcos_mul_left _ _ _ h1, dcos_mul_left _ _ _ h2, dcos_mul_right _ _ _ h1, dcos_mul_right _ _ _ h2]`.
-/
theorem isHecke_pair_double_coset {a b : ℕ} (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    IsHecke (I2 a b w) (dc2 w ϖ x y) := by
  obtain ⟨A, hA, hA0⟩ := dcos_supp (m := a) (w := w) (tdiag ϖ x)
  obtain ⟨B, hB, hB0⟩ := dcos_supp (m := b) (w := w) (tdiag ϖ y)
  refine ⟨HasCompactSupport.intro (hA.prod hB) fun g hg => ?_, fun k hk g => ?_⟩
  · simp only [Set.mem_prod, not_and_or] at hg
    rcases hg with h | h
    · simp [dc2, hA0 _ h]
    · simp [dc2, hB0 _ h]
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
    refine ⟨?_, ?_⟩ <;> simp only [dc2, Prod.fst_mul, Prod.snd_mul, dcos_mul_left _ _ _ h1, dcos_mul_left _ _ _ h2,
      dcos_mul_right _ _ _ h1, dcos_mul_right _ _ _ h2]

end Hk

section Frame

variable {n : ℕ} (d : LocData E n)

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]`. Conclude with `GlobalTheory.SplitFlip.isOpen_KO`.
-/
theorem isOpen_KGL' (w : Pl E) (m : ℕ) : IsOpen (GlobalTheory.LFun.KGL w m : Set (GLw m w)) := by
  rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isOpen_KO

/- English proof (translation)
Use `show IsOpen (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set (GLw a w × GLw b w))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(isOpen_KGL' w a).prod (isOpen_KGL' w b)`.
-/
theorem isOpen_levelSubgroup' (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  show IsOpen (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set (GLw a w × GLw b w))
  rw [Subgroup.coe_prod]
  exact (isOpen_KGL' w a).prod (isOpen_KGL' w b)

/- English proof (translation)
Use `show IsOpen (((iwGL a w).prod (iwGL b w) : Subgroup _) : Set (GLw a w × GLw b w))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _).prod (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _)`.
-/
theorem isOpen_iwahori_pair (a b : ℕ) (w : Pl E) : IsOpen (I2 a b w : Set (GLw a w × GLw b w)) := by
  show IsOpen (((iwGL a w).prod (iwGL b w) : Subgroup _) : Set (GLw a w × GLw b w))
  rw [Subgroup.coe_prod]
  exact (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _).prod (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _)

/- English proof (translation)
The claim follows from `Subgroup.prod_mono (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w b)`.
-/
theorem iwahori_pair_le_maximal_pair (a b : ℕ) (w : Pl E) : I2 a b w ≤ K2 a b w :=
  Subgroup.prod_mono (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w b)

/- English proof (translation)
Take `⟨-, hT, hS, hB, -⟩` from `hw`. Establish `: w ∉ d.S₀ ∪ d.Bad` using `by simp [hS, hB]`. Simplify using `only [LocData.lev, if_neg hT, if_neg this]`.
-/
theorem lev_good {a : ℕ} {w : Pl E} (hw : d.Good w) : d.lev a w = K2 a (n - a) w := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  have : w ∉ d.S₀ ∪ d.Bad := by simp [hS, hB]
  simp only [LocData.lev, if_neg hT, if_neg this]

/- English proof (translation)
Take `⟨-, hT, hS, hB, -⟩` from `hw`. Establish `: w ∉ d.S₀ ∪ d.Bad` using `by simp [hS, hB]`. Simplify using `only [LocData.lev₂, if_neg this]`.
-/
theorem lev₂_good {a : ℕ} {w : Pl E} (hw : d.Good w) : d.lev₂ a w = K2 a (n - a) w := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  have : w ∉ d.S₀ ∪ d.Bad := by simp [hS, hB]
  simp only [LocData.lev₂, if_neg this]

/- English proof (translation)
Take `⟨hsp, -, -, -, hμ⟩` from `hw`. Establish `h` using `GlobalTheory.CompanionTheory.CtHecke.isHecke_ctT E n a (n - a) (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w) hsp (hd.unif w) hμ k`. Use `⟨h.1.mono fun y hy h0 => hy (by simp [LocData.hc, h0]), fun κ hκ x => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp only [LocData.hc, Pi.smul_apply, (h.2 κ hκ x).1, (h.2 κ hκ x).2]`.
-/
theorem hecke_hc (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : d.Good w) (k : ℕ) :
    IsHecke (K2 a (n - a) w) (d.hc a ha w k) := by
  obtain ⟨hsp, -, -, -, hμ⟩ := hw
  have h := GlobalTheory.CompanionTheory.CtHecke.isHecke_ctT E n a (n - a) (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w) hsp (hd.unif w) hμ k
  refine ⟨h.1.mono fun y hy h0 => hy (by simp [LocData.hc, h0]), fun κ hκ x => ?_⟩
  refine ⟨?_, ?_⟩ <;> simp only [LocData.hc, Pi.smul_apply, (h.2 κ hκ x).1, (h.2 κ hκ x).2]

def Slot (a : ℕ) (ha : a ≤ n) (w : Pl E) (Lv : Subgroup (GLw a w × GLw (n - a) w)) (f : LF a (n - a) w) : Prop :=
  f = idem Lv ∨ (d.Good w ∧ ∃ k, f = d.hc a ha w k)

/- English proof (translation)
Distinguish the cases in `hw : d.Good w`. Take `rfl` from `hLv hw`. Establish `hI` using `h1 E a (n - a) w (K2 a (n - a) w) (isOpen_levelSubgroup' a (n - a) w) le_rfl`. Establish `H : ∀ u, Slot d a ha w (K2 a (n - a) w) u → IsHecke (K2 a (n - a) w) u`. Introduce and unpack `u (rfl | ⟨-, k, rfl⟩)`.

Conclude with `hI.1`. Conclude with `hecke_hc d hd ha hw k`. Establish `Hf` using `H f hf`. Establish `Hg` using `H g hg`. Establish `Hg' : IsHecke (K2 a (n - a) w) (lfStar g)` using `((hI.2.2 g Hg).2.2)`.

Conclude with `⟨h2 E a (n - a) w f g Hf Hg, h2 E a (n - a) w f _ Hf Hg'⟩`. Establish `e : ∀ u, Slot d a ha w Lv u → u = idem Lv`. Introduce and unpack `u (rfl | ⟨h, -⟩)`. Both sides reduce to the same expression. Conclude with `absurd h hw`.

Rewrite using `[e f hf, e g hg, lfStar_idem]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem comm (h1 : IdemAlg) (h2 : SphComm) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E}
    {Lv : Subgroup (GLw a w × GLw (n - a) w)} (hLv : d.Good w → Lv = K2 a (n - a) w) {f g : LF a (n - a) w}
    (hf : Slot d a ha w Lv f) (hg : Slot d a ha w Lv g) :
    mconv f g = mconv g f ∧ mconv f (lfStar g) = mconv (lfStar g) f := by
  by_cases hw : d.Good w
  · obtain rfl := hLv hw
    have hI := h1 E a (n - a) w (K2 a (n - a) w) (isOpen_levelSubgroup' a (n - a) w) le_rfl
    have H : ∀ u, Slot d a ha w (K2 a (n - a) w) u → IsHecke (K2 a (n - a) w) u := by
      rintro u (rfl | ⟨-, k, rfl⟩)
      · exact hI.1
      · exact hecke_hc d hd ha hw k
    have Hf := H f hf
    have Hg := H g hg
    have Hg' : IsHecke (K2 a (n - a) w) (lfStar g) := ((hI.2.2 g Hg).2.2)
    exact ⟨h2 E a (n - a) w f g Hf Hg, h2 E a (n - a) w f _ Hf Hg'⟩
  · have e : ∀ u, Slot d a ha w Lv u → u = idem Lv := by
      rintro u (rfl | ⟨h, -⟩)
      · rfl
      · exact absurd h hw
    rw [e f hf, e g hg, lfStar_idem]
    exact ⟨rfl, rfl⟩

end Frame

section Main

variable {n : ℕ} (d : LocData E n)

/- English proof (translation)
Apply the tactic sequence `rcases hL with rfl | ⟨w, k, intersection_update_fsHerm_neg_one, -, rfl⟩ <;> rfl`.
-/
theorem gen_m {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) : L.m = (d.eL a).m := by
  rcases hL with rfl | ⟨w, k, intersection_update_fsHerm_neg_one, -, rfl⟩ <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `w x y`. Use `show lfStar (L.m w y x) = _`. Rewrite using `[gen_m d hL]`. Simplify using `only [LocData.eL, LocData.diag]`. Distinguish the cases in `h : x = y`.

Substitute `h` using the available equality. Simplify using `[lfStar_idem]`. Rewrite using `[if_neg (Ne.symm h), if_neg h, lfStar_zero]`.
-/
theorem adj_m {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) : L.adj.m = (d.eL a).m := by
  funext w x y
  show lfStar (L.m w y x) = _
  rw [gen_m d hL]
  simp only [LocData.eL, LocData.diag]
  by_cases h : x = y
  · subst h
    simp [lfStar_idem]
  · rw [if_neg (Ne.symm h), if_neg h, lfStar_zero]

/- English proof (translation)
Break down `hL with rfl | ⟨w', k, intersection_update_fsHerm_neg_one, hw', rfl⟩` into its components or cases. Conclude with `Or.inl rfl`. Consider the cases of `intersection_update_fsHerm_neg_one`. Distinguish the cases in `e : w = w'`. Substitute `e` using the available equality.

Conclude with `Or.inr ⟨hw', k, by simp [LocData.hL]⟩`. Conclude with `Or.inl (by simp [LocData.hL, Function.update_of_ne e, LocData.eL])`. Conclude with `Or.inl (by simp [LocData.hL, LocData.eL])`.
-/
theorem generator_first_levi_position {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) (w : Pl E) :
    Slot d a ha w (d.lev a w) (L.s w) := by
  rcases hL with rfl | ⟨w', k, intersection_update_fsHerm_neg_one, hw', rfl⟩
  · exact Or.inl rfl
  · cases intersection_update_fsHerm_neg_one
    · by_cases e : w = w'
      · subst e
        exact Or.inr ⟨hw', k, by simp [LocData.hL]⟩
      · exact Or.inl (by simp [LocData.hL, Function.update_of_ne e, LocData.eL])
    · exact Or.inl (by simp [LocData.hL, LocData.eL])

/- English proof (translation)
Break down `hL with rfl | ⟨w', k, intersection_update_fsHerm_neg_one, hw', rfl⟩` into its components or cases. Conclude with `Or.inl rfl`. Consider the cases of `intersection_update_fsHerm_neg_one`. Conclude with `Or.inl (by simp [LocData.hL, LocData.eL])`. Distinguish the cases in `e : w = w'`.

Substitute `e` using the available equality. Conclude with `Or.inr ⟨hw', k, by simp [LocData.hL]⟩`. Conclude with `Or.inl (by simp [LocData.hL, Function.update_of_ne e, LocData.eL])`.
-/
theorem generator_second_levi_position {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) (w : Pl E) :
    Slot d a ha w (d.lev₂ a w) (L.t w) := by
  rcases hL with rfl | ⟨w', k, intersection_update_fsHerm_neg_one, hw', rfl⟩
  · exact Or.inl rfl
  · cases intersection_update_fsHerm_neg_one
    · exact Or.inl (by simp [LocData.hL, LocData.eL])
    · by_cases e : w = w'
      · subst e
        exact Or.inr ⟨hw', k, by simp [LocData.hL]⟩
      · exact Or.inl (by simp [LocData.hL, Function.update_of_ne e, LocData.eL])

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single y]`. Simplify using `[LocData.diag]`. Introduce `z _ hz`. Simplify using `[LocData.diag, hz, mconv_zero_right]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ y) h`.
-/
theorem sum_diag_right {a : ℕ} {w : Pl E} (M : d.kap w → d.kap w → LF a (n - a) w) (f : LF a (n - a) w)
    (x y : d.kap w) : ∑ z, mconv (M x z) (d.diag (fun _ => f) z y) = mconv (M x y) f := by
  rw [Finset.sum_eq_single y]
  · simp [LocData.diag]
  · intro z _ hz
    simp [LocData.diag, hz, mconv_zero_right]
  · intro h
    exact absurd (Finset.mem_univ y) h

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single x]`. Simplify using `[LocData.diag]`. Introduce `z _ hz`. Simplify using `[LocData.diag, Ne.symm hz, mconv_zero_left]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ x) h`.
-/
theorem sum_diag_left {a : ℕ} {w : Pl E} (M : d.kap w → d.kap w → LF a (n - a) w) (f : LF a (n - a) w)
    (x y : d.kap w) : ∑ z, mconv (d.diag (fun _ => f) x z) (M z y) = mconv f (M x y) := by
  rw [Finset.sum_eq_single x]
  · simp [LocData.diag]
  · intro z _ hz
    simp [LocData.diag, Ne.symm hz, mconv_zero_left]
  · intro h
    exact absurd (Finset.mem_univ x) h

/- English proof (translation)
Distinguish the cases in `h : LocData.admitted n a s`. Establish `e : d.qT a w s = fun y => ∑ x ∈ (d.c w).support, (d.c w x * (-qh w) ^ (-vRes n a (lOf x) s) * (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ)) * dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y`. Use function extensionality and compare the values at `y`. Simplify using `only [LocData.qT, dif_pos h, Finsupp.sum]`. Rewrite using `[e]`.

Conclude with `isHecke_sum _ _ (fun x => d.c w x * (-qh w) ^ (-vRes n a (lOf x) s) * (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ)) (fun x y => dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y) fun x _ => isHecke_pair_double_coset _ _ _`. Establish `e : d.qT a w s = 0`. Use function extensionality and compare the values at `y`. Simplify using `only [LocData.qT, dif_neg h, Pi.zero_apply]`. Rewrite using `[e]`.

Conclude with `isHecke_zero _`.
-/
theorem hecke_qT {a : ℕ} (w : Pl E) (s : Finset (Fin (n / 2))) : IsHecke (I2 a (n - a) w) (d.qT a w s) := by
  by_cases h : LocData.admitted n a s
  · have e : d.qT a w s = fun y => ∑ x ∈ (d.c w).support, (d.c w x * (-qh w) ^ (-vRes n a (lOf x) s) *
        (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ)) *
          dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y := by
      funext y
      simp only [LocData.qT, dif_pos h, Finsupp.sum]
    rw [e]
    exact isHecke_sum _ _ (fun x => d.c w x * (-qh w) ^ (-vRes n a (lOf x) s) *
        (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ))
      (fun x y => dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y) fun x _ => isHecke_pair_double_coset _ _ _
  · have e : d.qT a w s = 0 := by
      funext y
      simp only [LocData.qT, dif_neg h, Pi.zero_apply]
    rw [e]
    exact isHecke_zero _

/- English proof (translation)
Simplify using `only [mul_comm, mul_left_comm]`.
-/
theorem rearr {G : Type} [CommMonoid G] (s p q r t : G) : s * (p * q) * (r * t) = s * q * t * (p * r) := by
  simp only [mul_comm, mul_left_comm]

/- English proof (translation)
Simplify using `only [mul_comm, mul_left_comm]`.
-/
theorem rearr' {G : Type} [CommMonoid G] (s p q r t : G) : s * (q * p) * (t * r) = s * q * t * (p * r) := by
  simp only [mul_comm, mul_left_comm]

/- English proof (translation)
Take `⟨hO, hle, hnor, hXK, huniq, hHk⟩` from `hd.K' w hw`. Take `⟨-, hcs, hinv⟩` from `(h3 n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) hO hle hnor (d.X w) hXK huniq).1 (d.e w) hHk x hx y hy`. Establish `hL` using `fun k (hk : k ∈ d.L a w) => hd.LS a ha w hw k hk`. Establish `h1` using `(hL 1 (one_mem _)).1`. Use `⟨HasCompactSupport.mono hcs fun m hm h0 => hm (by simp [LocData.mac, phiMu, h0]), fun k hk g => ?_⟩` and prove the remaining obligations.

Establish `hk'` using `hL k hk`. Establish `p1 : phi3 (Nat.add_sub_of_le ha) w (d.e w) x y (k * g) = phi3 (Nat.add_sub_of_le ha) w (d.e w) x y g`. Simplify using `using hinv k hk'.1 1 h1 g`. Establish `p2 : phi3 (Nat.add_sub_of_le ha) w (d.e w) x y (g * k) = phi3 (Nat.add_sub_of_le ha) w (d.e w) x y g`. Simplify using `using hinv 1 h1 k hk'.1 g`.

Establish `m1 : d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det (k * g).1 ^ (n - a) * GeneralLinearGroup.det (k * g).2 ^ a) = d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a)`. Establish `e : (-1) ^ (a * (n - a)) * GeneralLinearGroup.det (k * g).1 ^ (n - a) * GeneralLinearGroup.det (k * g).2 ^ a = ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) * (GeneralLinearGroup.det k.1 ^ (n - a) * GeneralLinearGroup.det k.2 ^ a)`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]`. Conclude with `rearr _ _ _ _ _`. Rewrite using `[e, map_mul, hk'.2, mul_one]`.

Establish `m2 : d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det (g * k).1 ^ (n - a) * GeneralLinearGroup.det (g * k).2 ^ a) = d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a)`. Establish `e : (-1) ^ (a * (n - a)) * GeneralLinearGroup.det (g * k).1 ^ (n - a) * GeneralLinearGroup.det (g * k).2 ^ a = ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) * (GeneralLinearGroup.det k.1 ^ (n - a) * GeneralLinearGroup.det k.2 ^ a)`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]`. Conclude with `rearr' _ _ _ _ _`. Rewrite using `[e, map_mul, hk'.2, mul_one]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LocData.mac, phiMu, p1, m1]`. Simplify using `only [LocData.mac, phiMu, p2, m2]`.
-/
theorem hecke_mac (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.S₀) {x y : GLw n w}
    (hx : x ∈ d.X w) (hy : y ∈ d.X w) : IsHecke (d.L a w) (d.mac a ha w (d.e w) x y) := by
  obtain ⟨hO, hle, hnor, hXK, huniq, hHk⟩ := hd.K' w hw
  obtain ⟨-, hcs, hinv⟩ := (h3 n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) hO hle hnor (d.X w) hXK huniq).1
    (d.e w) hHk x hx y hy
  have hL := fun k (hk : k ∈ d.L a w) => hd.LS a ha w hw k hk
  have h1 := (hL 1 (one_mem _)).1
  refine ⟨HasCompactSupport.mono hcs fun m hm h0 => hm (by simp [LocData.mac, phiMu, h0]), fun k hk g => ?_⟩
  have hk' := hL k hk
  have p1 : phi3 (Nat.add_sub_of_le ha) w (d.e w) x y (k * g) = phi3 (Nat.add_sub_of_le ha) w (d.e w) x y g := by
    simpa using hinv k hk'.1 1 h1 g
  have p2 : phi3 (Nat.add_sub_of_le ha) w (d.e w) x y (g * k) = phi3 (Nat.add_sub_of_le ha) w (d.e w) x y g := by
    simpa using hinv 1 h1 k hk'.1 g
  have m1 : d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det (k * g).1 ^ (n - a) * GeneralLinearGroup.det (k * g).2 ^ a) =
      d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) := by
    have e : (-1) ^ (a * (n - a)) * GeneralLinearGroup.det (k * g).1 ^ (n - a) * GeneralLinearGroup.det (k * g).2 ^ a =
        ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) *
          (GeneralLinearGroup.det k.1 ^ (n - a) * GeneralLinearGroup.det k.2 ^ a) := by
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
      exact rearr _ _ _ _ _
    rw [e, map_mul, hk'.2, mul_one]
  have m2 : d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det (g * k).1 ^ (n - a) * GeneralLinearGroup.det (g * k).2 ^ a) =
      d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) := by
    have e : (-1) ^ (a * (n - a)) * GeneralLinearGroup.det (g * k).1 ^ (n - a) * GeneralLinearGroup.det (g * k).2 ^ a =
        ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det g.1 ^ (n - a) * GeneralLinearGroup.det g.2 ^ a) *
          (GeneralLinearGroup.det k.1 ^ (n - a) * GeneralLinearGroup.det k.2 ^ a) := by
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
      exact rearr' _ _ _ _ _
    rw [e, map_mul, hk'.2, mul_one]
  refine ⟨?_, ?_⟩
  · simp only [LocData.mac, phiMu, p1, m1]
  · simp only [LocData.mac, phiMu, p2, m2]

/- English proof (translation)
Unfold `LocData.P at hw`. Distinguish the cases in `hT : w ∈ d.T`. Simplify using `only [LocData.lev, if_pos hT]`. Conclude with `⟨isOpen_iwahori_pair _ _ _, iwahori_pair_le_maximal_pair _ _ _⟩`. Establish `hS : w ∈ d.S₀` using `(Finset.mem_union.1 hw).resolve_left hT`.

Establish `hSB : w ∈ d.S₀ ∪ d.Bad` using `Finset.mem_union_left _ hS`. Take `⟨L₁, L₂, e, h1, h2⟩` from `hd.L a ha w hSB`. Simplify using `only [LocData.lev, if_neg hT, if_pos hSB, e]`. Use `⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_prod]`.

Conclude with `h1.1.prod h2.1`.
-/
theorem lev_ok (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.P) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
  unfold LocData.P at hw
  by_cases hT : w ∈ d.T
  · simp only [LocData.lev, if_pos hT]
    exact ⟨isOpen_iwahori_pair _ _ _, iwahori_pair_le_maximal_pair _ _ _⟩
  · have hS : w ∈ d.S₀ := (Finset.mem_union.1 hw).resolve_left hT
    have hSB : w ∈ d.S₀ ∪ d.Bad := Finset.mem_union_left _ hS
    obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hSB
    simp only [LocData.lev, if_neg hT, if_pos hSB, e]
    refine ⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩
    rw [Subgroup.coe_prod]
    exact h1.1.prod h2.1

/- English proof (translation)
Distinguish the cases in `hT : w ∈ d.T`. Establish `e : d.lev a w = I2 a (n - a) w` using `by simp [LocData.lev, hT]`. Rewrite using `[e]`. Use `show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _)`. Rewrite using `[if_pos hT]`.

Unfold `LocData.diag`. Use `split_ifs`. Conclude with `hecke_qT d w _`. Conclude with `isHecke_zero _`. Establish `hS : w ∈ d.S₀` using `(Finset.mem_union.1 hw).resolve_left hT`.

Establish `hSB : w ∈ d.S₀ ∪ d.Bad` using `Finset.mem_union_left _ hS`. Establish `e : d.lev a w = d.L a w` using `by simp [LocData.lev, hT, hSB]`. Rewrite using `[e]`. Use `show IsHecke _ (if w ∈ d.T then _ else d.mac a ha w (d.e w) x.1.2 y.1.2)`. Rewrite using `[if_neg hT]`.

Establish `hX : ∀ z : d.kap w, z.1.2 ∈ d.X w` using `fun z => by`. Use `z.2` as an intermediate fact. Simplify using `only [LocData.idx, if_neg hT, if_pos hS] at this`. Conclude with `(Finset.mem_product.1 this).2`. Conclude with `hecke_mac d h3 hd ha hS (hX x) (hX y)`.
-/
theorem hecke_beta (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.P) (x y : d.kap w) :
    IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  by_cases hT : w ∈ d.T
  · have e : d.lev a w = I2 a (n - a) w := by simp [LocData.lev, hT]
    rw [e]
    show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _)
    rw [if_pos hT]
    unfold LocData.diag
    split_ifs
    · exact hecke_qT d w _
    · exact isHecke_zero _
  · have hS : w ∈ d.S₀ := (Finset.mem_union.1 hw).resolve_left hT
    have hSB : w ∈ d.S₀ ∪ d.Bad := Finset.mem_union_left _ hS
    have e : d.lev a w = d.L a w := by simp [LocData.lev, hT, hSB]
    rw [e]
    show IsHecke _ (if w ∈ d.T then _ else d.mac a ha w (d.e w) x.1.2 y.1.2)
    rw [if_neg hT]
    have hX : ∀ z : d.kap w, z.1.2 ∈ d.X w := fun z => by
      have := z.2
      simp only [LocData.idx, if_neg hT, if_pos hS] at this
      exact (Finset.mem_product.1 this).2
    exact hecke_mac d h3 hd ha hS (hX x) (hX y)

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Use `show ∑ z, mconv ((d.betaL a ha).m w x z) (L.m w z y) = ∑ z, mconv (L.m w x z) ((d.betaL a ha).m w z y)`. Rewrite using `[hLm]`. Use `show ∑ z, mconv ((d.betaL a ha).m w x z) (d.diag (fun _ => idem (d.lev a w)) z y) = ∑ z, mconv (d.diag (fun _ => idem (d.lev a w)) x z) ((d.betaL a ha).m w z y)`. Rewrite using `[sum_diag_right, sum_diag_left]`.

Take `⟨ho, hle⟩` from `lev_ok d hd ha hw`. Establish `hI` using `(h1 E a (n - a) w _ ho hle).2.2 _ (hecke_beta d h3 hd ha hw x y)`. Rewrite using `[hI.1, hI.2.1]`.
-/
theorem beta_m (h1 : IdemAlg) (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.P)
    (L : LM d.kap a (n - a)) (hLm : L.m = (d.eL a).m) :
    ((d.betaL a ha).mul L).m w = (L.mul (d.betaL a ha)).m w := by
  funext x y
  show ∑ z, mconv ((d.betaL a ha).m w x z) (L.m w z y) = ∑ z, mconv (L.m w x z) ((d.betaL a ha).m w z y)
  rw [hLm]
  show ∑ z, mconv ((d.betaL a ha).m w x z) (d.diag (fun _ => idem (d.lev a w)) z y) =
    ∑ z, mconv (d.diag (fun _ => idem (d.lev a w)) x z) ((d.betaL a ha).m w z y)
  rw [sum_diag_right, sum_diag_left]
  obtain ⟨ho, hle⟩ := lev_ok d hd ha hw
  have hI := (h1 E a (n - a) w _ ho hle).2.2 _ (hecke_beta d h3 hd ha hw x y)
  rw [hI.1, hI.2.1]

end Main

end LocComm

open LocComm in
/- English proof (translation)
Introduce `E _ _ _ n d hd a ha L L' hL hL'`. Establish `hg : ∀ {w : Pl E}, d.Good w → d.lev a w = K2 a (n - a) w` using `fun h => LocComm.lev_good d h`. Establish `hg₂ : ∀ {w : Pl E}, d.Good w → d.lev₂ a w = K2 a (n - a) w` using `fun h => LocComm.lev₂_good d h`. Establish `e0 : ∀ w, LocComm.Slot d a ha w (d.lev a w) ((d.eL a).s w)` using `fun w => Or.inl rfl`. Establish `e1 : ∀ w, LocComm.Slot d a ha w (d.lev₂ a w) ((d.eL a).t w)` using `fun w => Or.inl rfl`.

Use `⟨⟨fun w _ => ?_, fun w _ => ?_, funext fun w => ?_⟩, ⟨fun w _ => ?_, fun w _ => ?_, funext fun w => ?_⟩, ⟨fun w hw => LocComm.beta_m d h1 (h3 E) hd ha hw L (LocComm.gen_m d hL), fun w _ => ?_, funext fun w => ?_⟩, ⟨fun w hw => LocComm.beta_m d h1 (h3 E) hd ha hw L.adj (LocComm.ad …` and prove the remaining obligations. Use `show (fun x y => ∑ z, mconv (L.m w x z) (L'.m w z y)) = fun x y => ∑ z, mconv (L'.m w x z) (L.m w z y)`. Rewrite using `[LocComm.gen_m d hL, LocComm.gen_m d hL']`. Conclude with `(LocComm.comm d h1 h2 hd ha hg (LocComm.generator_first_levi_position d hL w) (LocComm.generator_first_levi_position d hL' w)).1`. Conclude with `(LocComm.comm d h1 h2 hd ha hg₂ (LocComm.generator_second_levi_position d hL w) (LocComm.generator_second_levi_position d hL' w)).1`.

Use `show (fun x y => ∑ z, mconv (L.m w x z) (L'.adj.m w z y)) = fun x y => ∑ z, mconv (L'.adj.m w x z) (L.m w z y)`. Rewrite using `[LocComm.gen_m d hL, LocComm.adj_m d hL']`. Conclude with `(LocComm.comm d h1 h2 hd ha hg (LocComm.generator_first_levi_position d hL w) (LocComm.generator_first_levi_position d hL' w)).2`. Conclude with `(LocComm.comm d h1 h2 hd ha hg₂ (LocComm.generator_second_levi_position d hL w) (LocComm.generator_second_levi_position d hL' w)).2`. Conclude with `(LocComm.comm d h1 h2 hd ha hg (e0 w) (LocComm.generator_first_levi_position d hL w)).1`.

Conclude with `(LocComm.comm d h1 h2 hd ha hg₂ (e1 w) (LocComm.generator_second_levi_position d hL w)).1`. Conclude with `(LocComm.comm d h1 h2 hd ha hg (e0 w) (LocComm.generator_first_levi_position d hL w)).2`. Conclude with `(LocComm.comm d h1 h2 hd ha hg₂ (e1 w) (LocComm.generator_second_levi_position d hL w)).2`.
-/
theorem locComm (h1 : IdemAlg) (h2 : SphComm) (h3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) :
    LocComm := by
  intro E _ _ _ n d hd a ha L L' hL hL'
  have hg : ∀ {w : Pl E}, d.Good w → d.lev a w = K2 a (n - a) w := fun h => LocComm.lev_good d h
  have hg₂ : ∀ {w : Pl E}, d.Good w → d.lev₂ a w = K2 a (n - a) w := fun h => LocComm.lev₂_good d h
  have e0 : ∀ w, LocComm.Slot d a ha w (d.lev a w) ((d.eL a).s w) := fun w => Or.inl rfl
  have e1 : ∀ w, LocComm.Slot d a ha w (d.lev₂ a w) ((d.eL a).t w) := fun w => Or.inl rfl
  refine ⟨⟨fun w _ => ?_, fun w _ => ?_, funext fun w => ?_⟩, ⟨fun w _ => ?_, fun w _ => ?_, funext fun w => ?_⟩,
    ⟨fun w hw => LocComm.beta_m d h1 (h3 E) hd ha hw L (LocComm.gen_m d hL), fun w _ => ?_, funext fun w => ?_⟩,
    ⟨fun w hw => LocComm.beta_m d h1 (h3 E) hd ha hw L.adj (LocComm.adj_m d hL), fun w _ => ?_, funext fun w => ?_⟩⟩
  · show (fun x y => ∑ z, mconv (L.m w x z) (L'.m w z y)) = fun x y => ∑ z, mconv (L'.m w x z) (L.m w z y)
    rw [LocComm.gen_m d hL, LocComm.gen_m d hL']
  · exact (LocComm.comm d h1 h2 hd ha hg (LocComm.generator_first_levi_position d hL w) (LocComm.generator_first_levi_position d hL' w)).1
  · exact (LocComm.comm d h1 h2 hd ha hg₂ (LocComm.generator_second_levi_position d hL w) (LocComm.generator_second_levi_position d hL' w)).1
  · show (fun x y => ∑ z, mconv (L.m w x z) (L'.adj.m w z y)) = fun x y => ∑ z, mconv (L'.adj.m w x z) (L.m w z y)
    rw [LocComm.gen_m d hL, LocComm.adj_m d hL']
  · exact (LocComm.comm d h1 h2 hd ha hg (LocComm.generator_first_levi_position d hL w) (LocComm.generator_first_levi_position d hL' w)).2
  · exact (LocComm.comm d h1 h2 hd ha hg₂ (LocComm.generator_second_levi_position d hL w) (LocComm.generator_second_levi_position d hL' w)).2
  · exact (LocComm.comm d h1 h2 hd ha hg (e0 w) (LocComm.generator_first_levi_position d hL w)).1
  · exact (LocComm.comm d h1 h2 hd ha hg₂ (e1 w) (LocComm.generator_second_levi_position d hL w)).1
  · exact (LocComm.comm d h1 h2 hd ha hg (e0 w) (LocComm.generator_first_levi_position d hL w)).2
  · exact (LocComm.comm d h1 h2 hd ha hg₂ (e1 w) (LocComm.generator_second_levi_position d hL w)).2

end PositivityTheory.Rg.BcB.F

end
