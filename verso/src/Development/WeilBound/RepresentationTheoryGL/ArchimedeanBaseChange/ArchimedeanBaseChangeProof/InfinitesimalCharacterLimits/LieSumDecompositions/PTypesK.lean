import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section KAux

def k_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) : GL (Fin b) R := h ▸ g

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem k_castGL_apply {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) (i j : Fin b) :
    (k_castGL h g : Matrix (Fin b) (Fin b) R) i j = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem k_castGL_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) :
    k_castGL h.symm (k_castGL h g) = g := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Conclude with `InducedTensorMap.B.lev_cc (s := 0) (g, 1) i j`.
-/
theorem levi_embed_left_zero {R : Type} [CommRing R] {r : ℕ} (g : GL (Fin r) R) : lev R r 0 (g, 1) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact InducedTensorMap.B.lev_cc (s := 0) (g, 1) i j

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Take `⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i'` from `⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩`. Take `⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j'` from `⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩`. Rewrite using `[InducedTensorMap.B.lev_nn (r := 0) (1, u) i' j', k_castGL_apply]`. Establish `e : ∀ x : Fin s, Fin.cast (Nat.zero_add s).symm.symm (Fin.natAdd 0 x) = x` using `fun x => Fin.ext (by simp)`.

Rewrite using `[e, e]`.
-/
theorem k_lev_0s {R : Type} [CommRing R] {s : ℕ} (u : GL (Fin s) R) :
    lev R 0 s (1, u) = k_castGL (Nat.zero_add s).symm u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i' := ⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j' := ⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩
  rw [InducedTensorMap.B.lev_nn (r := 0) (1, u) i' j', k_castGL_apply]
  have e : ∀ x : Fin s, Fin.cast (Nat.zero_add s).symm.symm (Fin.natAdd 0 x) = x := fun x => Fin.ext (by simp)
  rw [e, e]

omit [IsCMField E] in
/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hu`.
-/
theorem k_mem_cast {F : ∀ n : ℕ, Subgroup (GL (Fin n) (Af E))} {a b : ℕ} (h : a = b) {u : GL (Fin a) (Af E)}
    (hu : u ∈ F a) : k_castGL h u ∈ F b := by
  subst h; exact hu

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[Subgroup.coe_inf]`. Conclude with `h.inter h'`.
-/
theorem k_isOpen_inf {G : Type} [Group G] [TopologicalSpace G] {H H' : Subgroup G} (h : IsOpen (H : Set G))
    (h' : IsOpen (H' : Set G)) : IsOpen ((H ⊓ H' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]; exact h.inter h'

omit [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite h`.
-/
theorem k_isOpen_iInf {G : Type} [Group G] [TopologicalSpace G] {ι : Sort*} [Finite ι] {H : ι → Subgroup G}
    (h : ∀ i, IsOpen (H i : Set G)) : IsOpen ((⨅ i, H i : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite h

end KAux

open Classical in

def Tset (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))) : Finset (GL (Fin (r + s)) (Af E)) :=
  if r = 0 ∨ s = 0 then {1} else if h : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) then
    Classical.choose (IwaAd.iwasawa_finite_cosets E r s L h) else ∅

/- English proof (translation)
Distinguish the cases in `hr : r = 0 ∨ s = 0`. Establish `hT : Tset r s L = {1}` using `by rw [Tset, if_pos hr]`. Break down `hr with rfl | rfl` into its components or cases. Use `⟨0, (1, k_castGL (Nat.zero_add s) g), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[InducedTensorMap.unip_zero, k_lev_0s, k_castGL_castGL, map_one, map_one, map_one]`.

Simplify using the standard rewrite rules. Use `⟨0, (g, 1), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[InducedTensorMap.unip_zero, levi_embed_left_zero, map_one, map_one, map_one]`. Simplify using the standard rewrite rules. Establish `hT : Tset r s L = Classical.choose (IwaAd.iwasawa_finite_cosets E r s L hL)`.

Rewrite using `[Tset, if_neg hr, dif_pos hL]`. Rewrite using `[hT]`. Conclude with `Classical.choose_spec (IwaAd.iwasawa_finite_cosets E r s L hL) g`.
-/
theorem Tset_spec {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E))
      (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ Tset r s L ∧ l ∈ L ∧
      g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  by_cases hr : r = 0 ∨ s = 0
  · have hT : Tset r s L = {1} := by rw [Tset, if_pos hr]
    rcases hr with rfl | rfl
    · refine ⟨0, (1, k_castGL (Nat.zero_add s) g), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, k_lev_0s, k_castGL_castGL, map_one, map_one, map_one]
      simp
    · refine ⟨0, (g, 1), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, levi_embed_left_zero, map_one, map_one, map_one]
      simp
  · have hT : Tset r s L = Classical.choose (IwaAd.iwasawa_finite_cosets E r s L hL) := by
      rw [Tset, if_neg hr, dif_pos hL]
    rw [hT]
    exact Classical.choose_spec (IwaAd.iwasawa_finite_cosets E r s L hL) g

def topK (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  if h : n = N then h ▸ K else ⊤

def Kf (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  topK N K n ⊓ detKer n ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N),
      ⨅ t : {t // t ∈ Tset n s (Kf N K (n + s))}, Slice1.levelOne s (Kf N K (n + s)) t.1) ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N),
      ⨅ t : {t // t ∈ Tset s n (Kf N K (s + n))}, Slice2.L₂ s (Kf N K (s + n)) t.1)
termination_by N - n
decreasing_by all_goals omega

variable {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))}

/- English proof (translation)
Use the proof step `induction' hd : N - n using Nat.strong_induction_on with d ih generalizing n`. Rewrite using `[Kf]`. Use `k_isOpen_inf (k_isOpen_inf (k_isOpen_inf ?_ (isOpen_detKer n)) ?_) ?_` and prove the remaining obligations. Unfold `topK split_ifs with h`. Substitute `h` using the available equality.

Conclude with `hK`. Rewrite using `[Subgroup.coe_top]`. Conclude with `isOpen_univ`. Use `k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_` and prove the remaining obligations. Conclude with `Slice1.isOpen_levelOne (ih _ (by omega) _ rfl) _`.

Use `k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_` and prove the remaining obligations. Conclude with `Slice2.isOpen_L₂ (ih _ (by omega) _ rfl) _`.
-/
theorem isOpen_Kf (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (n : ℕ) :
    IsOpen (Kf N K n : Set (GL (Fin n) (Af E))) := by
  induction' hd : N - n using Nat.strong_induction_on with d ih generalizing n
  rw [Kf]
  refine k_isOpen_inf (k_isOpen_inf (k_isOpen_inf ?_ (isOpen_detKer n)) ?_) ?_
  · unfold topK
    split_ifs with h
    · subst h; exact hK
    · rw [Subgroup.coe_top]; exact isOpen_univ
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice1.isOpen_levelOne (ih _ (by omega) _ rfl) _
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice2.isOpen_L₂ (ih _ (by omega) _ rfl) _

/- English proof (translation)
Rewrite using `[Kf]`. Conclude with `inf_le_left.trans (inf_le_left.trans inf_le_right)`.
-/
theorem Kf_le_det (n : ℕ) : Kf N K n ≤ detKer n := by
  rw [Kf]
  exact inf_le_left.trans (inf_le_left.trans inf_le_right)

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[Kf]`. Establish `h` using `hu.1.1.1`. Unfold `topK at h`. Rewrite `h` using `[dif_pos rfl]`.

Conclude with `h`.
-/
theorem Kf_top : Kf N K N ≤ K := by
  intro u hu
  rw [Kf] at hu
  have h := hu.1.1.1
  unfold topK at h
  rw [dif_pos rfl] at h
  exact h

/- English proof (translation)
Break down `Nat.eq_zero_or_pos s with rfl | hs` into its components or cases. Establish `hT : Tset r 0 (Kf N K (r + 0)) = {1}` using `by rw [Tset, if_pos (Or.inr rfl)]`. Rewrite `ht` using `[hT, Finset.mem_singleton]`. Substitute `ht` using the available equality. Rewrite using `[inv_one, one_mul, mul_one, levi_embed_left_zero]`.

Conclude with `hu`. Rewrite `hu` using `[Kf]`. Establish `h` using `(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2`. Rewrite `h` using `[Subgroup.mem_iInf]`. Establish `h2` using `h ⟨s, by omega⟩`.

Rewrite `h2` using `[Subgroup.mem_iInf]`. Establish `h3` using `h2 ⟨hs, hN⟩`. Rewrite `h3` using `[Subgroup.mem_iInf]`. Conclude with `Slice1.mem_levelOne.1 (h3 ⟨t, ht⟩)`.
-/
theorem Kf_left {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin r) (Af E)} (hu : u ∈ Kf N K r) : t⁻¹ * lev (Af E) r s (u, 1) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hT : Tset r 0 (Kf N K (r + 0)) = {1} := by rw [Tset, if_pos (Or.inr rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, levi_embed_left_zero]
    exact hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨s, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hs, hN⟩
    rw [Subgroup.mem_iInf] at h3
    exact Slice1.mem_levelOne.1 (h3 ⟨t, ht⟩)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Establish `hT : Tset 0 s (Kf N K (0 + s)) = {1}` using `by rw [Tset, if_pos (Or.inl rfl)]`. Rewrite `ht` using `[hT, Finset.mem_singleton]`. Substitute `ht` using the available equality. Rewrite using `[inv_one, one_mul, mul_one, k_lev_0s]`.

Conclude with `k_mem_cast (F := Kf N K) (Nat.zero_add s).symm hu`. Rewrite `hu` using `[Kf]`. Establish `h` using `(Subgroup.mem_inf.1 hu).2`. Rewrite `h` using `[Subgroup.mem_iInf]`. Establish `h2` using `h ⟨r, by omega⟩`.

Rewrite `h2` using `[Subgroup.mem_iInf]`. Establish `h3` using `h2 ⟨hr, hN⟩`. Rewrite `h3` using `[Subgroup.mem_iInf]`. Establish `h4` using `h3 ⟨t, ht⟩`. Simplify `h4` using `[Slice2.L₂, Slice2.lev2, MulAut.conj_apply]`.
-/
theorem Kf_right {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin s) (Af E)} (hu : u ∈ Kf N K s) : t⁻¹ * lev (Af E) r s (1, u) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hT : Tset 0 s (Kf N K (0 + s)) = {1} := by rw [Tset, if_pos (Or.inl rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, k_lev_0s]
    exact k_mem_cast (F := Kf N K) (Nat.zero_add s).symm hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 hu).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨r, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hr, hN⟩
    rw [Subgroup.mem_iInf] at h3
    have h4 := h3 ⟨t, ht⟩
    simpa [Slice2.L₂, Slice2.lev2, MulAut.conj_apply] using h4

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
