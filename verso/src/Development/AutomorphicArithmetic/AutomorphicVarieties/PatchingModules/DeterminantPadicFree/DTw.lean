import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DerEv

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Set `S' : LinearMap.range T →ₗ[F] M` to `((LinearMap.ker T).liftQ S h).comp T.quotKerEquivRange.symm.toLinearMap`. Take `⟨d, hd⟩` from `LinearMap.exists_extend S'`. Use `⟨d, fun c => ?_⟩` and prove the remaining obligations. Establish `h1 : d (T c) = S' ⟨T c, LinearMap.mem_range_self T c⟩`. Rewrite using `[← hd]`.

Both sides reduce to the same expression. Establish `h2 : T.quotKerEquivRange.symm ⟨T c, LinearMap.mem_range_self T c⟩ = Submodule.Quotient.mk c`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[LinearMap.quotKerEquivRange_apply_mk]`.

Rewrite using `[h1]`. Simplify using `only [S', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]`.
-/
private theorem exists_factor {F A M : Type} [Field F] [AddCommGroup A] [Module F A] [AddCommGroup M] [Module F M]
    (T S : A →ₗ[F] M) (h : LinearMap.ker T ≤ LinearMap.ker S) : ∃ d : M →ₗ[F] M, ∀ c, d (T c) = S c := by
  let S' : LinearMap.range T →ₗ[F] M :=
    ((LinearMap.ker T).liftQ S h).comp T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨d, hd⟩ := LinearMap.exists_extend S'
  refine ⟨d, fun c => ?_⟩
  have h1 : d (T c) = S' ⟨T c, LinearMap.mem_range_self T c⟩ := by
    rw [← hd]
    rfl
  have h2 : T.quotKerEquivRange.symm ⟨T c, LinearMap.mem_range_self T c⟩ = Submodule.Quotient.mk c := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [h1]
  simp only [S', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

/- English proof (translation)
Introduce `F G _ _ n D z hz hk`. Set `A` to `Finsupp.supported F F (D.G' : Set G)`. Set `T : A →ₗ[F] Matrix (Fin n) (Fin n) F` to `(Finsupp.linearCombination F (fun g => D.r g)).comp A.subtype`. Set `S : A →ₗ[F] Matrix (Fin n) (Fin n) F` to `(Finsupp.linearCombination F (fun g => z g * D.r g)).comp A.subtype`. Establish `hTS : LinearMap.ker T ≤ LinearMap.ker S`.

Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Use extensionality with `i j`. Establish `hsupp : ∀ g ∈ (c : G →₀ F).support, g ∈ D.G'` using `fun g hg => (Finsupp.mem_supported F _).1 c.2 hg`. Use `hk i j (c : G →₀ F) hsupp (by simpa [T, Finsupp.linearCombination_apply] using hc)` as an intermediate fact.

Simplify `this` using `[S, Finsupp.linearCombination_apply]`. Take `⟨d, hd⟩` from `exists_factor T S hTS`. Establish `hdr : ∀ g ∈ D.G', d (D.r g) = z g * D.r g`. Introduce `g hg`. Use `hd ⟨Finsupp.single g 1, Finsupp.single_mem_supported F 1 hg⟩` as an intermediate fact.

Simplify `this` using `[T, S]`. Establish `hr1 : ∀ g, D.r g⁻¹ * D.r g = 1` using `fun g => by`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Establish `hgen : ∀ g ∈ D.G', ∀ h ∈ D.G', d (D.r g * D.r h) = d (D.r g) * D.r h + D.r g * d (D.r h)`. Introduce `g hg h hh`.

Rewrite using `[← D.r.map_mul, hdr _ (D.G'.mul_mem hg hh), hdr g hg, hdr h hh, hz g hg h hh, D.r.map_mul]`. Simplify using `only [one_smul, Matrix.add_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (D.r g⁻¹) (D.r g) (D.r h), hr1, Matrix.one_mul]`. Establish `hder : ∀ x ∈ Ev F F n D.a, ∀ y ∈ Ev F F n D.a, d (x * y) = d x * y + x * d y`. Introduce `x hx y hy`.

Rewrite `hx`, `hy` using `[← D.span]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx'`. Take `⟨g, hg, rfl⟩` from `hx'`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy'`. Take `⟨h, hh, rfl⟩` from `hy'`. Conclude with `hgen g hg h hh`. Consider the case `zero => simp`. Consider the case `add y1 y2 _ _ h1 h2`.

Simplify using `only [Matrix.mul_add, map_add, h1, h2]`. Normalize the expressions using the abelian group laws. Consider the case `smul a y _ h1`. Simplify using `only [Matrix.mul_smul, map_smul, h1, smul_add]`. Consider the case `zero => simp`.

Consider the case `add x1 x2 _ _ h1 h2`. Simplify using `only [Matrix.add_mul, map_add, h1, h2]`. Normalize the expressions using the abelian group laws. Consider the case `smul a x _ h1`. Simplify using `only [Matrix.smul_mul, map_smul, h1, smul_add]`.

Take `⟨Y, hY⟩` from `Det.derEv d hder`. Use `⟨-Y, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h1` using `hY (D.r g) (D.ev g)`. Rewrite `h1` using `[hdr g hg]`. Establish `h2 : z g = (Y * D.r g - D.r g * Y) * D.r g⁻¹`.

Rewrite using `[← h1, Matrix.mul_assoc, ← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]`. Rewrite using `[h2]`. Simplify using `only [dTw, one_smul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Rewrite using `[← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.Pa.Det.der :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r D.G' z → (∀ i j, D.KillsRel z i j) → ∃ Y, ∀ g ∈ D.G', z g = dTw (fun _ => 1) D.r Y g := by
  intro F G _ _ n D z hz hk
  let A := Finsupp.supported F F (D.G' : Set G)
  let T : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => D.r g)).comp A.subtype
  let S : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => z g * D.r g)).comp A.subtype
  have hTS : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    ext i j
    have hsupp : ∀ g ∈ (c : G →₀ F).support, g ∈ D.G' := fun g hg =>
      (Finsupp.mem_supported F _).1 c.2 hg
    have := hk i j (c : G →₀ F) hsupp (by simpa [T, Finsupp.linearCombination_apply] using hc)
    simpa [S, Finsupp.linearCombination_apply] using this
  obtain ⟨d, hd⟩ := exists_factor T S hTS
  have hdr : ∀ g ∈ D.G', d (D.r g) = z g * D.r g := by
    intro g hg
    have := hd ⟨Finsupp.single g 1, Finsupp.single_mem_supported F 1 hg⟩
    simpa [T, S] using this
  have hr1 : ∀ g, D.r g⁻¹ * D.r g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hgen : ∀ g ∈ D.G', ∀ h ∈ D.G',
      d (D.r g * D.r h) = d (D.r g) * D.r h + D.r g * d (D.r h) := by
    intro g hg h hh
    rw [← D.r.map_mul, hdr _ (D.G'.mul_mem hg hh), hdr g hg, hdr h hh, hz g hg h hh, D.r.map_mul]
    simp only [one_smul, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹) (D.r g) (D.r h), hr1, Matrix.one_mul]
  have hder : ∀ x ∈ Ev F F n D.a, ∀ y ∈ Ev F F n D.a, d (x * y) = d x * y + x * d y := by
    intro x hx y hy
    rw [← D.span] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨g, hg, rfl⟩ := hx'
      induction hy using Submodule.span_induction with
      | mem y hy' =>
        obtain ⟨h, hh, rfl⟩ := hy'
        exact hgen g hg h hh
      | zero => simp
      | add y1 y2 _ _ h1 h2 =>
        simp only [Matrix.mul_add, map_add, h1, h2]
        abel
      | smul a y _ h1 =>
        simp only [Matrix.mul_smul, map_smul, h1, smul_add]
    | zero => simp
    | add x1 x2 _ _ h1 h2 =>
      simp only [Matrix.add_mul, map_add, h1, h2]
      abel
    | smul a x _ h1 =>
      simp only [Matrix.smul_mul, map_smul, h1, smul_add]
  obtain ⟨Y, hY⟩ := Det.derEv d hder
  refine ⟨-Y, fun g hg => ?_⟩
  have h1 := hY (D.r g) (D.ev g)
  rw [hdr g hg] at h1
  have h2 : z g = (Y * D.r g - D.r g * Y) * D.r g⁻¹ := by
    rw [← h1, Matrix.mul_assoc, ← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [h2]
  simp only [dTw, one_smul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  abel
