import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluingExistence

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Conclude with `⟨0, by simpa using hx⟩`. Rewrite using `[Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩`.

Consider the case `algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Establish `: (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n` using `by ring`. Rewrite using `[this]`. Conclude with `C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))`. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`.

Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m)` using `by ring`. Rewrite using `[this]`. Conclude with `C.mul_mem hn hm`.
-/
theorem mul_pow_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (x : L) (hx : x ∈ Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    ∃ n : ℕ, x * v ^ n ∈ C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n := by ring
    rw [this]; exact C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m) := by ring
    rw [this]; exact C.mul_mem hn hm

/- English proof (translation)
Use `letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra`. Establish `hvi : v⁻¹ ∈ E` using `hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, n, rfl⟩`. Use `isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show (v ^ n) * (v⁻¹) ^ n = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hv0, one_pow]`. Introduce and unpack `⟨z, hz⟩`. Take `⟨n, hn⟩` from `mul_pow_mem C v hv hv0 z (hE ▸ hz)`. Conclude with `⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩`.

Introduce `x y h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: (x : L) = y` using `congrArg (fun w : E => (w : L)) h`. Simplify using `[Subtype.ext this]`.
-/
theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C E : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (hCE : C ≤ E) (hE : E = Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
    IsLocalization.Away (⟨v, hv⟩ : C) E := by
  letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
  have hvi : v⁻¹ ∈ E := hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩
    show (v ^ n) * (v⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := mul_pow_mem C v hv hv0 z (hE ▸ hz)
    exact ⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun w : E => (w : L)) h
    simp [Subtype.ext this]

/- English proof (translation)
Introduce `Ω L _ _ _ A B u h`. Take `⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩` from `h`. Use `set D := Dr Ω A u`. Establish `hAD : A ≤ D` using `le_Dr_A A u`. Establish `hBD : B ≤ D` using `le_Dr_B A B u hadj`.

Use `letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra`. Use `letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra`. Use `haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl`. Use `haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)`. Set `fA : Sp D ⟶ Sp A` to `Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)`.

Set `fB : Sp D ⟶ Sp B` to `Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)`. Use `haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)`. Use `haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)`. Use `haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by`. Introduce `i j f`.

Break down `f with _ | j` into its components or cases. Conclude with `inferInstanceAs (IsOpenImmersion (𝟙 _))`. Break down `j with _ | _` into its components or cases. Conclude with `hfA`. Conclude with `hfB`.

Establish `hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) = fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B))`. Simplify using `only [fA, fB, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `⟨{ C0 := pushout fA fB c0 := pushout.desc _ _ hc iA := pushout.inl fA fB iB := pushout.inr fA fB hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _)) hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _)) hcA := pushout.inl_desc _ _ _ hcB := pushout.in …` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]`. Take `⟨i, xi, rfl⟩` from `Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x`. Break down `i with _ | j` into its components or cases. Use `left`. Use `⟨fA xi, ?_⟩` and prove the remaining obligations.

Rewrite using `[← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]`. Both sides reduce to the same expression. Break down `j with _ | _` into its components or cases. Use `left`. Conclude with `⟨xi, rfl⟩`.

Use `right`. Conclude with `⟨xi, rfl⟩`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, rfl⟩, ⟨b, hb⟩⟩`.

Establish `hab : colimit.ι (span fA fB) (some WalkingPair.left) a = colimit.ι (span fA fB) (some WalkingPair.right) b` using `hb.symm`. Take `⟨k, fi, fj, y, hy1, hy2⟩` from `(Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab`. Break down `k with _ | k` into its components or cases. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]`.

Both sides reduce to the same expression. Break down `k with _ | _` into its components or cases. Consider the cases of `(show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)`. Consider the cases of `(show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)`. Introduce and unpack `⟨y, rfl⟩`.

Use `⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩` and prove the remaining obligations. Use `show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y`. Rewrite using `[pushout.condition]`.
-/
theorem LeafGlueExists_of : LeafGlueExists := by
  intro Ω L _ _ _ A B u h
  obtain ⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩ := h
  set D := Dr Ω A u
  have hAD : A ≤ D := le_Dr_A A u
  have hBD : B ≤ D := le_Dr_B A B u hadj
  letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra
  letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl
  haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D :=
    away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)
  let fA : Sp D ⟶ Sp A := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)
  let fB : Sp D ⟶ Sp B := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)
  haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)
  haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)
  haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by
    intro i j f
    rcases f with _ | j
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · rcases j with _ | _
      · exact hfA
      · exact hfB
  have hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
      fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    simp only [fA, fB, ← Spec.map_comp]; rfl
  refine ⟨{
    C0 := pushout fA fB
    c0 := pushout.desc _ _ hc
    iA := pushout.inl fA fB
    iB := pushout.inr fA fB
    hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hcA := pushout.inl_desc _ _ _
    hcB := pushout.inr_desc _ _ _
    agree := pushout.condition
    cover := ?_
    inter := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x
    rcases i with _ | j
    · left; refine ⟨fA xi, ?_⟩
      rw [← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
    · rcases j with _ | _
      · left; exact ⟨xi, rfl⟩
      · right; exact ⟨xi, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : colimit.ι (span fA fB) (some WalkingPair.left) a =
          colimit.ι (span fA fB) (some WalkingPair.right) b := hb.symm
      obtain ⟨k, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab
      rcases k with _ | k
      · refine ⟨y, ?_⟩
        rw [← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
      · rcases k with _ | _
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)
    · rintro ⟨y, rfl⟩
      refine ⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩
      show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y
      rw [pushout.condition]

end LateralTheory.E.GluingExistence
