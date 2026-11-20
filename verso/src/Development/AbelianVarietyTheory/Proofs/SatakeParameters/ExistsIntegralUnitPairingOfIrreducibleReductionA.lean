import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory.Cong.UnitPairing

open IsLocalRing

variable {R k : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
  [Algebra R k] [IsFractionRing R k] {a : ℕ}

noncomputable def intLattice (W : Submodule k (Fin a → k)) : Submodule R (Fin a → R) :=
  (W.restrictScalars R).comap ((Algebra.linearMap R k).compLeft (Fin a))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_intLattice {W : Submodule k (Fin a → k)} {x : Fin a → R} :
    x ∈ intLattice (R := R) W ↔ (fun i => algebraMap R k (x i)) ∈ W := Iff.rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
/- English proof (translation)
Rewrite `*` using `[mem_intLattice]`. Establish `h' : algebraMap R k r • (fun i => algebraMap R k (x i)) ∈ W`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[Algebra.smul_def]`.

Conclude with `(W.smul_mem_iff ((map_ne_zero_iff _ (IsFractionRing.injective R k)).mpr hr)).mp h'`.
-/
lemma mem_intLattice_of_smul {W : Submodule k (Fin a → k)} {r : R} (hr : r ≠ 0)
    {x : Fin a → R} (h : r • x ∈ intLattice (R := R) W) : x ∈ intLattice (R := R) W := by
  rw [mem_intLattice] at *
  have h' : algebraMap R k r • (fun i => algebraMap R k (x i)) ∈ W := by
    convert h using 1
    ext i
    simp [Algebra.smul_def]
  exact (W.smul_mem_iff ((map_ne_zero_iff _ (IsFractionRing.injective R k)).mpr hr)).mp h'

omit [IsDiscreteValuationRing R] in
/- English proof (translation)
Take `⟨⟨b, hb⟩, h⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ y`. Use `choose x hx using fun i => h i (Finset.mem_univ i)`. Use `⟨b, nonZeroDivisors.ne_zero hb, x, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[hx i]`.

Simplify using `[Algebra.smul_def]`.
-/
lemma exists_integral_multiple (y : Fin a → k) :
    ∃ d : R, d ≠ 0 ∧ ∃ x : Fin a → R,
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y := by
  classical
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ y
  choose x hx using fun i => h i (Finset.mem_univ i)
  refine ⟨b, nonZeroDivisors.ne_zero hb, x, ?_⟩
  ext i
  rw [hx i]
  simp [Algebra.smul_def]

noncomputable def redLattice (L : Submodule R (Fin a → R)) :
    Submodule (ResidueField R) (Fin a → ResidueField R) where
  carrier := {v | ∃ x ∈ L, (fun i => residue R (x i)) = v}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, L.add_mem hx hy, by ext i; simp⟩
  zero_mem' := ⟨0, L.zero_mem, by ext i; simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨r • x, L.smul_mem r hx, by ext i; simp⟩

omit [IsFractionRing R k] in
/- English proof (translation)
Establish `: ∀ i, ϖ ∣ x i` using `fun i => by`. Establish `h1 : residue R (x i) = 0` using `congrFun h i`. Rewrite `h1` using `[residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton]`. Conclude with `h1`. Use `choose z hz using this`.

Conclude with `⟨z, funext fun i => by simp [hz i]⟩`.
-/
lemma exists_eq_smul_of_residue_eq_zero {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {x : Fin a → R} (h : (fun i => residue R (x i)) = 0) : ∃ z : Fin a → R, x = ϖ • z := by
  have : ∀ i, ϖ ∣ x i := fun i => by
    have h1 : residue R (x i) = 0 := congrFun h i
    rw [residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton] at h1
    exact h1
  choose z hz using this
  exact ⟨z, funext fun i => by simp [hz i]⟩

/- English proof (translation)
Take `⟨ϖ, hϖirr⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hϖ : maximalIdeal R = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr`. Establish `hϖ0 : ϖ ≠ 0` using `hϖirr.ne_zero`. Establish `hϖm : ϖ ∈ maximalIdeal R` using `hϖ ▸ Ideal.mem_span_singleton_self ϖ`. Establish `hϖres : residue R ϖ = 0` using `(residue_eq_zero_iff ϖ).mpr hϖm`.

Establish `hinj` using `IsFractionRing.injective R k`. Use `set L := intLattice (R := R) W with hLdef`. Use `haveI : NoZeroSMulDivisors R ((Fin a → R) ⧸ L) := by`. Use `⟨fun {r q} h => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective L q`.

Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero L).mpr (mem_intLattice_of_smul hr h)`.

Use `haveI : Module.Free R ((Fin a → R) ⧸ L) := Module.free_of_finite_type_torsion_free'`. Establish `hmemL : ∀ {y : Fin a → k}, y ∈ W → ∀ {d : R} {x : Fin a → R}, (fun i => algebraMap R k (x i)) = algebraMap R k d • y → x ∈ L`. Introduce `y hy d x hx`. Use `show (fun i => algebraMap R k (x i)) ∈ W`. Rewrite using `[hx]`.

Conclude with `W.smul_mem _ hy`. Establish `hA : redLattice L ≠ ⊥`. Introduce `hbot`. Establish `hle : L ≤ maximalIdeal R • L`. Introduce `x hx`.

Establish `h0 : (fun i => residue R (x i)) = 0`. Establish `hm : (fun i => residue R (x i)) ∈ redLattice L` using `⟨x, hx, rfl⟩`. Rewrite `hm` using `[hbot]`. Conclude with `(Submodule.mem_bot _).mp hm`. Take `⟨z, rfl⟩` from `exists_eq_smul_of_residue_eq_zero hϖ h0`.

Conclude with `Submodule.smul_mem_smul hϖm (mem_intLattice_of_smul hϖ0 hx)`. Establish `hL : L = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) L (IsNoetherian.noetherian L) hle (maximalIdeal_le_jacobson _)`. Take `⟨y, hyW, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Take `⟨d, hd, x, hx⟩` from `exists_integral_multiple (R := R) y`. Establish `hxL` using `hmemL hyW hx`.

Rewrite `hxL` using `[hL, Submodule.mem_bot]`. Substitute `hxL` using the available equality. Establish `h2 : algebraMap R k d • y = 0`. Rewrite using `[← hx]`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `hd (hinj (by simpa using h))`. Conclude with `hy0 h`. Establish `hT : redLattice L ≠ ⊤`.

Introduce `htop`. Establish `hle : (⊤ : Submodule R ((Fin a → R) ⧸ L)) ≤ maximalIdeal R • ⊤`. Introduce `q _`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective L q`. Establish `hm : (fun i => residue R (x i)) ∈ redLattice L` using `htop ▸ Submodule.mem_top`.

Take `⟨l, hl, hlx⟩` from `hm`. Establish `h0 : (fun i => residue R ((x - l) i)) = 0`. Use extensionality with `i`. Use `congrFun hlx i` as an intermediate fact. Simplify using `only [Pi.sub_apply, map_sub, Pi.zero_apply] at this ⊢`.

Rewrite using `[this, sub_self]`. Take `⟨z, hz⟩` from `exists_eq_smul_of_residue_eq_zero hϖ h0`. Establish `hq : Submodule.Quotient.mk (p` using `L) x = ϖ • Submodule.Quotient.mk z := by`. Rewrite using `[← Submodule.Quotient.mk_smul, ← hz, Submodule.Quotient.eq, sub_sub_cancel]`. Conclude with `hl`.

Rewrite using `[hq]`. Conclude with `Submodule.smul_mem_smul hϖm Submodule.mem_top`. Establish `htopQ` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤ Module.Finite.fg_top hle (maximalIdeal_le_jacobson _)`. Apply `hWt` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Take `⟨d, hd, x, hx⟩` from `exists_integral_multiple (R := R) y`. Establish `hxL : x ∈ L`. Establish `h1 : Submodule.Quotient.mk (p` using `L) x ∈ (⊤ : Submodule R ((Fin a → R) ⧸ L)) := Submodule.mem_top`. Rewrite `h1` using `[htopQ]`.

Conclude with `(Submodule.Quotient.mk_eq_zero L).mp ((Submodule.mem_bot _).mp h1)`. Establish `hdy : algebraMap R k d • y ∈ W`. Rewrite using `[← hx]`. Conclude with `hxL`. Conclude with `(W.smul_mem_iff ((map_ne_zero_iff _ hinj).mpr hd)).mp hdy`.

Establish `hnot : ∃ v ∈ redLattice L, (B.map (residue R)).mulVec v ∉ redLattice L`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Break down `hB _ hcon with h | h` into its components or cases. Conclude with `hA h`.

Conclude with `hT h`. Take `⟨_, ⟨w, hwL, rfl⟩, hBw⟩` from `hnot`. Establish `hres : (B.map (residue R)).mulVec (fun i => residue R (w i)) = fun i => residue R (B.mulVec w i)`. Use extensionality with `i`. Conclude with `(RingHom.map_mulVec (residue R) B w i).symm`.

Rewrite `hBw` using `[hres]`. Establish `hnotsmul : ∀ z : Fin a → R, Submodule.Quotient.mk (p` using `L) (B.mulVec w) ≠ ϖ • Submodule.Quotient.mk z := by`. Introduce `z hz`. Rewrite `hz` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Apply `hBw` to reduce the goal to its premises.

Use `⟨B.mulVec w - ϖ • z, hz, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[hϖres]`. Set `b` to `Module.Free.chooseBasis R ((Fin a → R) ⧸ L)`. Establish `hj : ∃ j, b.repr (Submodule.Quotient.mk (B.mulVec w)) j ∉ maximalIdeal R`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hdv : ∀ j, ϖ ∣ b.repr (Submodule.Quotient.mk (B.mulVec w)) j` using `fun j => by`. Use `hcon j` as an intermediate fact. Rewrite `this` using `[hϖ, Ideal.mem_span_singleton]`. Then use the resulting hypothesis.

Use `choose c hc using hdv`. Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective L (b.repr.symm (Finsupp.equivFunOnFinite.symm c))`. Apply `hnotsmul z` to reduce the goal to its premises. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `j`.

Rewrite using `[hc j, hz, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul]`. Simplify using the standard rewrite rules. Take `⟨j, hjm⟩` from `hj`. Set `φ : (Fin a → R) →ₗ[R] R` to `(b.coord j).comp L.mkQ`. Establish `hφ : ∀ x, φ x = b.repr (Submodule.Quotient.mk x) j` using `fun x => by`.

Simplify using `[φ, Module.Basis.coord_apply]`. Set `f : Fin a → R` to `fun i => φ (fun j' => if i = j' then 1 else 0)`. Establish `hf : ∀ x, f ⬝ᵥ x = φ x`. Introduce `x`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ x, dotProduct]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[f, smul_eq_mul, mul_comm]`. Use `⟨w, f, hwL, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨d, hd, x, hx⟩` from `exists_integral_multiple (R := R) y`.

Establish `hxL` using `hmemL hy hx`. Establish `hφx : φ x = 0`. Rewrite using `[hφ, (Submodule.Quotient.mk_eq_zero L).mpr hxL, map_zero, Finsupp.zero_apply]`. Establish `e1 : (fun i => algebraMap R k (f i)) ⬝ᵥ (fun i => algebraMap R k (x i)) = algebraMap R k (f ⬝ᵥ x)`. Simplify using `[dotProduct, map_sum, map_mul]`.

Rewrite `e1` using `[hx, dotProduct_smul, smul_eq_mul, hf, hφx, map_zero]`. Break down `mul_eq_zero.mp e1 with h | h` into its components or cases. Conclude with `absurd h ((map_ne_zero_iff _ hinj).mpr hd)`. Conclude with `h`. Rewrite using `[hf, hφ]`.

Assume the negation of the conclusion as `hu`. Conclude with `hjm ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))`.
-/
theorem main (B : Matrix (Fin a) (Fin a) R)
    (hB : ∀ W : Submodule (ResidueField R) (Fin a → ResidueField R),
      (∀ v ∈ W, (B.map (residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧
      (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  classical
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖ0 : ϖ ≠ 0 := hϖirr.ne_zero
  have hϖm : ϖ ∈ maximalIdeal R := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hϖres : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖm
  have hinj := IsFractionRing.injective R k
  set L := intLattice (R := R) W with hLdef
  haveI : NoZeroSMulDivisors R ((Fin a → R) ⧸ L) := by
    refine ⟨fun {r q} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero L).mpr (mem_intLattice_of_smul hr h)
  haveI : Module.Free R ((Fin a → R) ⧸ L) := Module.free_of_finite_type_torsion_free'
  have hmemL : ∀ {y : Fin a → k}, y ∈ W → ∀ {d : R} {x : Fin a → R},
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y → x ∈ L := by
    intro y hy d x hx
    show (fun i => algebraMap R k (x i)) ∈ W
    rw [hx]
    exact W.smul_mem _ hy

  have hA : redLattice L ≠ ⊥ := by
    intro hbot
    have hle : L ≤ maximalIdeal R • L := by
      intro x hx
      have h0 : (fun i => residue R (x i)) = 0 := by
        have hm : (fun i => residue R (x i)) ∈ redLattice L := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (Submodule.mem_bot _).mp hm
      obtain ⟨z, rfl⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      exact Submodule.smul_mem_smul hϖm (mem_intLattice_of_smul hϖ0 hx)
    have hL : L = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) L
      (IsNoetherian.noetherian L) hle (maximalIdeal_le_jacobson _)
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hyW hx
    rw [hL, Submodule.mem_bot] at hxL
    subst hxL
    have h2 : algebraMap R k d • y = 0 := by
      rw [← hx]
      ext i
      simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact hd (hinj (by simpa using h))
    · exact hy0 h

  have hT : redLattice L ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Submodule R ((Fin a → R) ⧸ L)) ≤ maximalIdeal R • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
      have hm : (fun i => residue R (x i)) ∈ redLattice L := htop ▸ Submodule.mem_top
      obtain ⟨l, hl, hlx⟩ := hm
      have h0 : (fun i => residue R ((x - l) i)) = 0 := by
        ext i
        have := congrFun hlx i
        simp only [Pi.sub_apply, map_sub, Pi.zero_apply] at this ⊢
        rw [this, sub_self]
      obtain ⟨z, hz⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      have hq : Submodule.Quotient.mk (p := L) x = ϖ • Submodule.Quotient.mk z := by
        rw [← Submodule.Quotient.mk_smul, ← hz, Submodule.Quotient.eq, sub_sub_cancel]
        exact hl
      rw [hq]
      exact Submodule.smul_mem_smul hϖm Submodule.mem_top
    have htopQ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
      Module.Finite.fg_top hle (maximalIdeal_le_jacobson _)
    apply hWt
    rw [eq_top_iff]
    intro y _
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL : x ∈ L := by
      have h1 : Submodule.Quotient.mk (p := L) x ∈ (⊤ : Submodule R ((Fin a → R) ⧸ L)) :=
        Submodule.mem_top
      rw [htopQ] at h1
      exact (Submodule.Quotient.mk_eq_zero L).mp ((Submodule.mem_bot _).mp h1)
    have hdy : algebraMap R k d • y ∈ W := by
      rw [← hx]
      exact hxL
    exact (W.smul_mem_iff ((map_ne_zero_iff _ hinj).mpr hd)).mp hdy

  have hnot : ∃ v ∈ redLattice L, (B.map (residue R)).mulVec v ∉ redLattice L := by
    by_contra hcon
    push_neg at hcon
    rcases hB _ hcon with h | h
    · exact hA h
    · exact hT h
  obtain ⟨_, ⟨w, hwL, rfl⟩, hBw⟩ := hnot
  have hres : (B.map (residue R)).mulVec (fun i => residue R (w i)) =
      fun i => residue R (B.mulVec w i) := by
    ext i
    exact (RingHom.map_mulVec (residue R) B w i).symm
  rw [hres] at hBw
  have hnotsmul : ∀ z : Fin a → R,
      Submodule.Quotient.mk (p := L) (B.mulVec w) ≠ ϖ • Submodule.Quotient.mk z := by
    intro z hz
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hz
    apply hBw
    refine ⟨B.mulVec w - ϖ • z, hz, ?_⟩
    ext i
    simp [hϖres]
  let b := Module.Free.chooseBasis R ((Fin a → R) ⧸ L)
  have hj : ∃ j, b.repr (Submodule.Quotient.mk (B.mulVec w)) j ∉ maximalIdeal R := by
    by_contra hcon
    push_neg at hcon
    have hdv : ∀ j, ϖ ∣ b.repr (Submodule.Quotient.mk (B.mulVec w)) j := fun j => by
      have := hcon j
      rwa [hϖ, Ideal.mem_span_singleton] at this
    choose c hc using hdv
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective L
      (b.repr.symm (Finsupp.equivFunOnFinite.symm c))
    apply hnotsmul z
    apply b.repr.injective
    ext j
    rw [hc j, hz, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul]
    simp
  obtain ⟨j, hjm⟩ := hj
  let φ : (Fin a → R) →ₗ[R] R := (b.coord j).comp L.mkQ
  have hφ : ∀ x, φ x = b.repr (Submodule.Quotient.mk x) j := fun x => by
    simp [φ, Module.Basis.coord_apply]
  let f : Fin a → R := fun i => φ (fun j' => if i = j' then 1 else 0)
  have hf : ∀ x, f ⬝ᵥ x = φ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f, smul_eq_mul, mul_comm]
  refine ⟨w, f, hwL, ?_, ?_⟩
  · intro y hy
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hy hx
    have hφx : φ x = 0 := by
      rw [hφ, (Submodule.Quotient.mk_eq_zero L).mpr hxL, map_zero, Finsupp.zero_apply]
    have e1 : (fun i => algebraMap R k (f i)) ⬝ᵥ (fun i => algebraMap R k (x i)) =
        algebraMap R k (f ⬝ᵥ x) := by
      simp [dotProduct, map_sum, map_mul]
    rw [hx, dotProduct_smul, smul_eq_mul, hf, hφx, map_zero] at e1
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h ((map_ne_zero_iff _ hinj).mpr hd)
    · exact h
  · rw [hf, hφ]
    by_contra hu
    exact hjm ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))

end GlobalTheory.Cong.UnitPairing

namespace GlobalTheory.Cong

/- English proof (translation)
Introduce `R k _ _ _ _ _ _ a B hB W hW0 hWt`. Conclude with `UnitPairing.main B hB W hW0 hWt`.
-/
theorem exists_integral_unit_pairing_of_irreducible_reduction : ∀ (R k : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k] (a : ℕ) (B : Matrix (Fin a) (Fin a) R), (∀ W : Submodule (IsLocalRing.ResidueField R) (Fin a → IsLocalRing.ResidueField R), (∀ v ∈ W, (B.map (IsLocalRing.residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ W : Submodule k (Fin a → k), W ≠ ⊥ → W ≠ ⊤ → ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧ (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  intro R k _ _ _ _ _ _ a B hB W hW0 hWt
  exact UnitPairing.main B hB W hW0 hWt

end GlobalTheory.Cong
