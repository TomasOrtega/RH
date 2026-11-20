import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Establish `h` using `(W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective (gr_internal O X R W).submodule_iSupIndep)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]`. Introduce `x hx`.

Conclude with `⟨⟨x, W.part_le_A hx⟩, rfl⟩`.
-/
private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

/- English proof (translation)
Establish `h` using `congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)`. Rewrite `h` using `[AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]`. Rewrite using `[← h]`. Use `congr 1`. Rewrite using `[Set.image_union]`.

Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Use extensionality with `x`. Simplify using `[WPres.zA, WPres.z]`.
-/
private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

/- English proof (translation)
Establish `hz : ∀ i, W.z i ∈ maximalIdeal R`. Introduce `i`. Set `ψ : R →+* ResidueField O` to `(IsLocalRing.residue O).comp (W.origin org).toRingHom`. Establish `hψ : Function.Surjective ψ`. Introduce `y`.

Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective y`. Conclude with `⟨algebraMap O R a, by simp [ψ]⟩`. Establish `heq : RingHom.ker ψ = maximalIdeal R` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)`. Rewrite using `[← heq, RingHom.mem_ker]`. Simplify using `[ψ, WPres.z, WPres.origin_π]`.

Establish `hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π))`. Establish `h` using `(homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c (fun i => Submodule.mem_comap.mpr (hg i))).1`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `f`. Rewrite using `[RingHom.mem_ker, Ideal.mem_comap]`.

Use `show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)`. Rewrite using `[← ker, RingHom.mem_ker]`. Use `⟨W.quot π surj hhom, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Conclude with `Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)`.

Introduce `i show π (W.z i) ∈ maximalIdeal S`. Rewrite using `[← res_eq_zero_iff O S, res_map, res_eq_zero_iff]`. Conclude with `hz i`.
-/
private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D _ M`. Set `g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R` to `Sum.elim M.F (Sum.elim M.E M.Z)`. Set `cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ` to `Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))`. Establish `hg : ∀ i, g i ∈ M.W.part (cw i)`. Introduce and unpack `(i | i | i)`.

Conclude with `M.hF i`. Conclude with `M.hE i`. Conclude with `(M.hZ i).1`. Establish `hker : RingHom.ker M.π = Ideal.span (Set.range g)`. Rewrite using `[M.ker]`.

Simplify using `only [g, Set.Sum.elim_range, Set.union_assoc]`. Take `⟨WS, hpart, hzm⟩` from `quot_pres M.W M.org M.π M.surj g cw hg hker`. Establish `hp : WS.part = M.sPart` using `funext hpart`. Establish `hA : WS.A = M.SS`. Unfold `WPres.A Model.SS`.

Reduce the equality to equality of the corresponding arguments. Use `haveI := WS.fin`. Use `⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hx`.

Conclude with `⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩`. Rewrite using `[← hA, ← part_gen WS, ← hp]`. Use `congr 2`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
