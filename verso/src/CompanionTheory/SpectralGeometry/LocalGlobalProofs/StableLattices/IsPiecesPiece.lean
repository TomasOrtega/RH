import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hLin_apply (hh : IsHerm s h) (x y : V) : hLin hh x y = h x y := rfl

/- English proof (translation)
The claim follows from `map_sub (hLin hh x) y z`.
-/
theorem h_sub_right (hh : IsHerm s h) (x y z : V) : h x (y - z) = h x y - h x z :=
  map_sub (hLin hh x) y z

/- English proof (translation)
The claim follows from `map_zero (hLin hh x)`.
-/
theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := map_zero (hLin hh x)

/- English proof (translation)
Establish `: z - z' = 0`. Apply `hh.2.2.2` to reduce the goal to its premises. Introduce `y`. Rewrite using `[hh.2.2.1 y (z - z'), h_sub_right hh, H, sub_self, map_zero]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem eq_of_pair (hh : IsHerm s h) {z z' : V} (H : ∀ x, h x z = h x z') : z = z' := by
  have : z - z' = 0 := by
    apply hh.2.2.2
    intro y
    rw [hh.2.2.1 y (z - z'), h_sub_right hh, H, sub_self, map_zero]
  exact sub_eq_zero.1 this

/- English proof (translation)
Simplify using `using (map_ne_zero s).2 hδ`.
-/
theorem s_ne (hδ : δ ≠ 0) : s δ ≠ 0 := by
  simpa using (map_ne_zero s).2 hδ

/- English proof (translation)
Simplify using `[projE, hLin_apply, mul_smul]`.
-/
theorem projE_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projE hh δ e f i x = ((s δ)⁻¹ * h (f i) x) • e i := by
  simp [projE, hLin_apply, mul_smul]

/- English proof (translation)
Simplify using `[projF, hLin_apply, mul_smul]`.
-/
theorem projF_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projF hh δ e f i x = (δ⁻¹ * h (e i) x) • f i := by
  simp [projF, hLin_apply, mul_smul]

/- English proof (translation)
Rewrite using `[hh.2.2.1 (e j) (f i), hF.2.2.1 j i]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem h_f_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if j = i then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1 j i]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[projE_apply, h_f_e hh hF]`. Use `split_ifs`. Simplify using `[s_ne hδ]`. Simplify using the standard rewrite rules.
-/
theorem projE_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (e j) = if j = i then e i else 0 := by
  rw [projE_apply, h_f_e hh hF]
  split_ifs
  · simp [s_ne hδ]
  · simp

/- English proof (translation)
Rewrite using `[projE_apply, hF.2.1]`. Simplify using the standard rewrite rules.
-/
theorem projE_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (f j) = 0 := by
  rw [projE_apply, hF.2.1]; simp

/- English proof (translation)
Rewrite using `[projE_apply, (hF.2.2.2.1 w hw i).2]`. Simplify using the standard rewrite rules.
-/
theorem projE_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projE hh δ e f i w = 0 := by
  rw [projE_apply, (hF.2.2.2.1 w hw i).2]; simp

/- English proof (translation)
Rewrite using `[projF_apply, hF.1]`. Simplify using the standard rewrite rules.
-/
theorem projF_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (e j) = 0 := by
  rw [projF_apply, hF.1]; simp

/- English proof (translation)
Rewrite using `[projF_apply, hF.2.2.1 i j]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `[hδ]`. Simplify using `[hij, Ne.symm hij]`.
-/
theorem projF_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (f j) = if j = i then f i else 0 := by
  rw [projF_apply, hF.2.2.1 i j]
  by_cases hij : j = i
  · subst hij; simp [hδ]
  · simp [hij, Ne.symm hij]

/- English proof (translation)
Rewrite using `[projF_apply, (hF.2.2.2.1 w hw i).1]`. Simplify using the standard rewrite rules.
-/
theorem projF_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projF hh δ e f i w = 0 := by
  rw [projF_apply, (hF.2.2.2.1 w hw i).1]; simp

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Simplify using `[piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `[piece, projE_e hh hδ hF]`.

Simplify using `[piece, projE_e hh hδ hF, hij, Ne.symm hij]`. Simplify using `[piece, projF_e hh hF]`.
-/
theorem piece_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projE_e hh hδ hF]
    · simp [piece, projE_e hh hδ hF, hij, Ne.symm hij]
  · simp [piece, projF_e hh hF]

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Simplify using `[piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]`. Simplify using `[piece, projE_f hh hF]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using `[piece, projF_f hh hδ hF]`. Simplify using `[piece, projF_f hh hδ hF, hij, Ne.symm hij]`.
-/
theorem piece_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (f j) = if i = some (Sum.inr j) then f j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]
  · simp [piece, projE_f hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projF_f hh hδ hF]
    · simp [piece, projF_f hh hδ hF, hij, Ne.symm hij]

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Simplify using `[piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]`. Simplify using `[piece, projE_w hh hF _ hw]`. Simplify using `[piece, projF_w hh hF _ hw]`.
-/
theorem piece_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Idx l) {w : V} (hw : w ∈ W) :
    piece hh δ e f i w = if i = none then w else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]
  · simp [piece, projE_w hh hF _ hw]
  · simp [piece, projF_w hh hF _ hw]

/- English proof (translation)
Use extensionality with `x`. Take `⟨a, b, w, hwW, rfl⟩` from `hF.2.2.2.2.2 x`. Simplify using `[map_add, map_sum, he, hf, hw w hwW]`.
-/
theorem end_ext (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by
  ext x
  obtain ⟨a, b, w, hwW, rfl⟩ := hF.2.2.2.2.2 x
  simp [map_add, map_sum, he, hf, hw w hwW]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Use `end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)` and prove the remaining obligations. Apply the tactic sequence `simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply] split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]`. Apply the tactic sequence `simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply] split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]`.

Apply the tactic sequence `simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply] split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]`. Introduce `i`. Use `end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)` and prove the remaining obligations. Apply the tactic sequence `simp only [Module.End.mul_apply, piece_e hh hδ hF] split_ifs with h1 <;> simp_all [piece_e hh hδ hF]`. Apply the tactic sequence `simp only [Module.End.mul_apply, piece_f hh hδ hF] split_ifs with h1 <;> simp_all [piece_f hh hδ hF]`.

Apply the tactic sequence `simp only [Module.End.mul_apply, piece_w hh hF _ hw] split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]`. Use `end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)` and prove the remaining obligations. Simplify using `[LinearMap.sum_apply, piece_e hh hδ hF]`. Simplify using `[LinearMap.sum_apply, piece_f hh hδ hF]`. Simplify using `[LinearMap.sum_apply, piece_w hh hF _ hw]`.
-/
theorem isPieces_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]
  · intro i
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw]
      split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp [LinearMap.sum_apply, piece_e hh hδ hF]
    · simp [LinearMap.sum_apply, piece_f hh hδ hF]
    · simp [LinearMap.sum_apply, piece_w hh hF _ hw]

/- English proof (translation)
Take `⟨m, b, hb⟩` from `hΛ`. Rewrite `hx`, the goal using `[hb]`. Introduce `i`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]`. Conclude with `mul_le_one₀ hc (norm_nonneg _) (hx i)`.
-/
theorem lat_smul {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {c : L} (hc : ‖c‖ ≤ 1) {x : V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx i)

/- English proof (translation)
Use `(hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by` as an intermediate fact. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij], fun i => by simp, by simp [h_zero_right hh]⟩`.

Simplify `this` using `[Pi.single_apply, ite_smul]`.
-/
theorem e_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    e j ∈ Λ := by
  have := (hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], fun i => by simp, by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

/- English proof (translation)
Use `(hA 0 (Pi.single j 1) 0 W.zero_mem).2 ⟨fun i => by simp, fun i => by` as an intermediate fact. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij], by simp [h_zero_right hh]⟩`.

Simplify `this` using `[Pi.single_apply, ite_smul]`.
-/
theorem f_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    f j ∈ Λ := by
  have := (hA 0 (Pi.single j 1) 0 W.zero_mem).2 ⟨fun i => by simp, fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

/- English proof (translation)
Take `⟨a, b, w, hw, rfl⟩` from `hF.2.2.2.2.2 x`. Take `⟨ha, hb, hww⟩` from `(hA a b w hw).1 hx`. Break down `i with _ | i | i` into its components or cases. Establish `: piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w`. Simplify using `[map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]`.

Rewrite using `[this]`. Use `(hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩` as an intermediate fact. Simplify using `using this`. Establish `: piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i`. Simplify using `[map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]`.

Rewrite using `[this]`. Conclude with `lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)`. Establish `: piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i`. Simplify using `[map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]`. Rewrite using `[this]`.

Conclude with `lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)`.
-/
theorem piece_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (hA : IsAdapted h e f W (fun _ => 1) Λ)
    (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) {x : V} (hx : x ∈ Λ) :
    piece hh δ e f i x ∈ Λ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  obtain ⟨ha, hb, hww⟩ := (hA a b w hw).1 hx
  rcases i with _ | i | i
  · have : piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    have := (hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩
    simpa using this
  · have : piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)
  · have : piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)

/- English proof (translation)
Take `⟨t1, t2, t3⟩` from `ht`. Prove the components needed by the constructor for the conclusion. Use `end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe] split_ifs with h1`. Substitute `h1` using the available equality.

Simplify using `[tau, t1]`. Simplify using the standard rewrite rules. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe] split_ifs with h1`. Substitute `h1` using the available equality. Simplify using `[tau, t2]`.

Simplify using the standard rewrite rules. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe] split_ifs with h1`. Substitute `h1` using the available equality. Simplify using `[tau, t3 w hw]`. Simplify using the standard rewrite rules.

Use `end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul, piece_e hh hδ hF] split_ifs with h1`. Substitute `h1` using the available equality. Simplify using `[tau]`. Simplify using the standard rewrite rules.

Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul, piece_f hh hδ hF] split_ifs with h1`. Substitute `h1` using the available equality. Simplify using `[tau]`. Simplify using the standard rewrite rules. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw, piece_w hh hF _ hw] split_ifs with h1`.

Substitute `h1` using the available equality. Simplify using `[tau]`. Simplify using the standard rewrite rules.
-/
theorem tor_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by
  obtain ⟨t1, t2, t3⟩ := ht
  constructor
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t1]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t2]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t3 w hw]
      · simp
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul,
        piece_e hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul,
        piece_f hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw,
        piece_w hh hF _ hw]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp

/- English proof (translation)
Apply the tactic sequence `rcases i with _ | i | i <;> simp only [wt] <;> omega`.
-/
theorem wt_le {l : ℕ} (i : Idx l) : wt i ≤ 2 * l := by
  rcases i with _ | i | i <;> simp only [wt] <;> omega

/- English proof (translation)
Apply the tactic sequence `rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;> first`. Consider the case `rfl`. Consider the case `(exfalso; have := i.2; omega)`. Consider the case `(exfalso; have := j.2; omega)`. Consider the case `(exfalso; have := i.2; have := j.2; omega)`.

Consider the case `(congr 2; apply Fin.ext; have := i.2; have := j.2; omega)`.
-/
theorem wt_injective {l : ℕ} : Function.Injective (wt : Idx l → ℕ) := by
  rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;>
    first
    | rfl
    | (exfalso; have := i.2; omega)
    | (exfalso; have := j.2; omega)
    | (exfalso; have := i.2; have := j.2; omega)
    | (congr 2; apply Fin.ext; have := i.2; have := j.2; omega)

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Simplify using `only [wt, rev]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [wt, rev]`. Use `i.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [wt, rev]`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem wt_rev {l : ℕ} (i : Idx l) : wt (rev i) + wt i = 2 * l := by
  rcases i with _ | i | i
  · simp only [wt, rev]; omega
  · simp only [wt, rev]; have := i.2; omega
  · simp only [wt, rev]; have := i.2; omega

/- English proof (translation)
Apply the tactic sequence `rcases i with _ | i | i <;> rfl`.
-/
theorem rev_rev {l : ℕ} (i : Idx l) : rev (rev i) = i := by
  rcases i with _ | i | i <;> rfl

/- English proof (translation)
Establish `hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖` using `fun m => by`. Rewrite using `[norm_inv, hs.2.1]`. Conclude with `(one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)`. Apply the tactic sequence `rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]`. Simplify using the standard rewrite rules.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `using hinv j`. Simplify using `using h1 i`. Establish `hij' : i ≤ j` using `by rw [Fin.le_def]; exact hij`.

Conclude with `hm hij'`. Conclude with `(h1 i).trans (hinv j)`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[norm_inv, norm_inv, hs.2.1, hs.2.1]`. Use `inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)` and prove the remaining obligations. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Rewrite using `[Fin.le_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem tau_mono (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by
  have hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖ := fun m => by
    rw [norm_inv, hs.2.1]
    exact (one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)
  rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]
  · simp
  · have := j.2; omega
  · simpa using hinv j
  · simpa using h1 i
  · have hij' : i ≤ j := by rw [Fin.le_def]; exact hij
    exact hm hij'
  · exact (h1 i).trans (hinv j)
  · have := i.2; omega
  · have := i.2; have := j.2; omega
  · rw [norm_inv, norm_inv, hs.2.1, hs.2.1]
    refine inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)
    have := i.2; have := j.2
    rw [Fin.le_def]; omega

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Simplify using `[tau]`. Simplify `hu0 i` using `[tau]`. Simplify `hu0 i` using `[tau]`.
-/
theorem tau_ne {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (i : Idx l) : tau s u i ≠ 0 := by
  rcases i with _ | i | i
  · simp [tau]
  · simpa [tau] using hu0 i
  · simpa [tau] using hu0 i

/- English proof (translation)
Rewrite using `[hh.2.2.1 y (c • x), hh.2.1, map_mul, ← hh.2.2.1 y x]`.
-/
theorem h_smul_left (hh : IsHerm s h) (c : L) (x y : V) : h (c • x) y = s c * h x y := by
  rw [hh.2.2.1 y (c • x), hh.2.1, map_mul, ← hh.2.2.1 y x]

/- English proof (translation)
Rewrite using `[hh.2.2.1 y (x + x'), hh.1, map_add, ← hh.2.2.1 y x, ← hh.2.2.1 y x']`.
-/
theorem h_add_left (hh : IsHerm s h) (x x' y : V) : h (x + x') y = h x y + h x' y := by
  rw [hh.2.2.1 y (x + x'), hh.1, map_add, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

/- English proof (translation)
Rewrite using `[hh.2.2.1 y 0, h_zero_right hh, map_zero]`.
-/
theorem h_zero_left (hh : IsHerm s h) (y : V) : h 0 y = 0 := by
  rw [hh.2.2.1 y 0, h_zero_right hh, map_zero]

/- English proof (translation)
The claim follows from `map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A`.
-/
theorem h_sum_left (hh : IsHerm s h) {ι : Type} (A : Finset ι) (v : ι → V) (y : V) :
    h (∑ m ∈ A, v m) y = ∑ m ∈ A, h (v m) y :=
  map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A

/- English proof (translation)
Rewrite using `[hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']`.
-/
theorem h_sub_left (hh : IsHerm s h) (x x' y : V) : h (x - x') y = h x y - h x' y := by
  rw [hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

/- English proof (translation)
Rewrite using `[projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem projE_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projE hh δ e f i x) y = h x (projF hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]
  ring

/- English proof (translation)
Rewrite using `[projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, ← hh.2.2.1 (e i) x]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem projF_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projF hh δ e f i x) y = h x (projE hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, ← hh.2.2.1 (e i) x]
  ring

/- English proof (translation)
Break down `i with _ | i | i` into its components or cases. Establish `hx` using `map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ`. Simplify using `only [hLin_apply] at hx`. Simplify using `only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1, projE_adj hs hh, projF_adj hs hh]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun m _ => add_comm _ _`. Conclude with `projE_adj hs hh i x y`. Conclude with `projF_adj hs hh i x y`.
-/
theorem piece_adj (hs : IsInv s) (hh : IsHerm s h) (i : Idx l) (x y : V) :
    h (piece hh δ e f i x) y = h x (piece hh δ e f (rev i) y) := by
  rcases i with _ | i | i
  · have hx := map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ
    simp only [hLin_apply] at hx
    simp only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1,
      projE_adj hs hh, projF_adj hs hh]
    congr 1
    exact Finset.sum_congr rfl fun m _ => add_comm _ _
  · exact projE_adj hs hh i x y
  · exact projF_adj hs hh i x y

/- English proof (translation)
Use `choose st hst using hadj`. Use `⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Use `eq_of_pair hh fun x => ?_` and prove the remaining obligations. Rewrite using `[← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]`.

Use extensionality with `y`. Use `eq_of_pair hh fun x => ?_` and prove the remaining obligations. Rewrite using `[← hst]`. Both sides reduce to the same expression. Use extensionality with `y`.

Use `eq_of_pair hh fun x => ?_` and prove the remaining obligations. Rewrite using `[← hst]`. Simplify using `[h_zero_left hh, h_zero_right hh]`. Use extensionality with `y`. Use `eq_of_pair hh fun x => ?_` and prove the remaining obligations.

Rewrite using `[← hst, piece_adj hs hh]`.
-/
theorem exists_star (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by
  choose st hst using hadj
  refine ⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; rfl
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; simp [h_zero_left hh, h_zero_right hh]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, piece_adj hs hh]

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
