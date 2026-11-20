import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FormsFin

open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V)

@[reducible] def act : MulAction Γ (G ⧸ B.U) := MulAction.compHom _ B.ι

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z hz g => by rwa [Subgroup.mem_center_iff.1 (B.cenΓ hz) g, mul_inv_cancel_right]⟩`.
-/
theorem normal0 : B.Γ₀.Normal := ⟨fun z hz g => by rwa [Subgroup.mem_center_iff.1 (B.cenΓ hz) g, mul_inv_cancel_right]⟩

/- English proof (translation)
Introduce `z hz y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H g => show ((B.ι z * g : G) : G ⧸ B.U) = g`. Rewrite using `[← Subgroup.mem_center_iff.1 (B.cenG z hz) g]`. Conclude with `QuotientGroup.mk_mul_of_mem _ (B.memU z hz)`.
-/
theorem triv0 : letI := act B; ∀ z ∈ B.Γ₀, ∀ y : G ⧸ B.U, z • y = y := by
  intro z hz y
  induction y using QuotientGroup.induction_on with
  | H g =>
    show ((B.ι z * g : G) : G ⧸ B.U) = g
    rw [← Subgroup.mem_center_iff.1 (B.cenG z hz) g]
    exact QuotientGroup.mk_mul_of_mem _ (B.memU z hz)

/- English proof (translation)
Use `letI := act B`. Introduce `y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H g`. Use `hB.stab g` and compare the differences between its conclusion and the goal.

Use extensionality with `γ`. Rewrite using `[mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.mem_map_equiv]`. Use `show ((B.ι γ * g : G) : G ⧸ B.U) = g ↔ _`. Rewrite using `[eq_comm, QuotientGroup.eq]`. Simplify using `[mul_assoc]`.
-/
theorem stab0 (hB : B.Fin) : letI := act B; ∀ y : G ⧸ B.U, B.Γ₀.relIndex (stabilizer Γ y) ≠ 0 := by
  letI := act B
  intro y
  induction y using QuotientGroup.induction_on with
  | H g =>
    convert hB.stab g
    ext γ
    rw [mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.mem_map_equiv]
    show ((B.ι γ * g : G) : G ⧸ B.U) = g ↔ _
    rw [eq_comm, QuotientGroup.eq]; simp [mul_assoc]

/- English proof (translation)
Use `letI := act B`. Take `⟨S, hS⟩` from `hB.cls`. Use `Finite.of_surjective (fun s : S => (Quotient.mk'' ((s : G) : G ⧸ B.U) : orbitRel.Quotient Γ (G ⧸ B.U))) ?_` and prove the remaining obligations. Introduce and unpack `⟨y⟩`. Proceed by induction on `y using QuotientGroup.induction_on with`.

Consider the case `H g`. Take `⟨γ, s, hs, u, hu, rfl⟩` from `hS g`. Use `⟨⟨s, hs⟩, Eq.symm (Quotient.sound ?_)⟩` and prove the remaining obligations. Conclude with `⟨γ, (QuotientGroup.mk_mul_of_mem _ hu).symm⟩`.
-/
theorem finQ (hB : B.Fin) : letI := act B; Finite (orbitRel.Quotient Γ (G ⧸ B.U)) := by
  letI := act B
  obtain ⟨S, hS⟩ := hB.cls
  refine Finite.of_surjective (fun s : S => (Quotient.mk'' ((s : G) : G ⧸ B.U) : orbitRel.Quotient Γ (G ⧸ B.U))) ?_
  rintro ⟨y⟩
  induction y using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
    refine ⟨⟨s, hs⟩, Eq.symm (Quotient.sound ?_)⟩
    exact ⟨γ, (QuotientGroup.mk_mul_of_mem _ hu).symm⟩

variable {B} (s : B.Tw) (f : G → ℂ)

noncomputable def Tk (g y : G) (γ : Γ) : Module.End ℂ V := f (g⁻¹ * s.θ (B.ι γ * y)) • (s.Θ ∘ₗ B.W γ)

variable {s f}

/- English proof (translation)
Use extensionality with `v`. Use `hf.right ⟨_, B.memU z hz⟩ (g⁻¹ * s.θ (B.ι γ * y))` as an intermediate fact. Simplify using `only [Tk, LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[map_mul B.ι, mul_assoc (B.ι γ), ← Subgroup.mem_center_iff.1 (B.cenG z hz) y, ← mul_assoc (B.ι γ), map_mul s.θ _ (B.ι z), ← mul_assoc, this, map_mul B.W, Module.End.mul_apply, B.scal z hz, map_smul, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]`. Simplify using the standard rewrite rules.
-/
theorem twistedKernelSummand_mul_trivialActing (hf : s.IsTest f) (g y : G) (γ : Γ) {z : Γ} (hz : z ∈ B.Γ₀) : Tk s f g y (γ * z) = Tk s f g y γ := by
  ext v
  have := hf.right ⟨_, B.memU z hz⟩ (g⁻¹ * s.θ (B.ι γ * y))
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_mul B.ι, mul_assoc (B.ι γ), ← Subgroup.mem_center_iff.1 (B.cenG z hz) y, ← mul_assoc (B.ι γ), map_mul s.θ _ (B.ι z), ← mul_assoc,
    this, map_mul B.W, Module.End.mul_apply, B.scal z hz, map_smul, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]
  simp

/- English proof (translation)
Take `⟨z, hz⟩` from `QuotientGroup.mk_out_eq_mul B.Γ₀ γ`. Rewrite using `[hz, mul_inv_rev, ← Subgroup.mem_center_iff.1 (B.cenΓ (inv_mem z.2)), twistedKernelSummand_mul_trivialActing hf _ _ _ (inv_mem z.2)]`.
-/
theorem Tk_out (hf : s.IsTest f) (g y : G) (γ : Γ) : Tk s f g y ((γ : Γ ⧸ B.Γ₀).out)⁻¹ = Tk s f g y γ⁻¹ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ γ
  rw [hz, mul_inv_rev, ← Subgroup.mem_center_iff.1 (B.cenΓ (inv_mem z.2)), twistedKernelSummand_mul_trivialActing hf _ _ _ (inv_mem z.2)]

def HD (s : B.Tw) (f : G → ℂ) : Prop :=
  ∀ g g' : G, ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z

/- English proof (translation)
Take `⟨D, hD⟩` from `hD g y`. Use `(D.finite_toSet.image fun d => (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀)).subset fun x hx => ?_` and prove the remaining obligations. Take `⟨d, hd, z, hz, h⟩` from `hD (s.θΓ x.out⁻¹) (by rwa [← s.comm, mul_assoc, ← map_mul])`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Establish `: s.θΓ.symm d = x.out⁻¹ * z⁻¹`.

Rewrite using `[MulEquiv.symm_apply_eq, map_mul, h, s.fix _ (inv_mem hz), mul_inv_cancel_right]`. Use `show (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x`. Rewrite using `[this, mul_inv_rev, inv_inv, inv_inv, ← Subgroup.mem_center_iff.1 (B.cenΓ hz), QuotientGroup.mk_mul_of_mem _ hz, QuotientGroup.out_eq']`.
-/
theorem f_fin (hD : HD s f) (g y : G) : {x : Γ ⧸ B.Γ₀ | f (g⁻¹ * s.θ (B.ι x.out⁻¹ * y)) ≠ 0}.Finite := by
  obtain ⟨D, hD⟩ := hD g y
  refine (D.finite_toSet.image fun d => (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀)).subset fun x hx => ?_
  obtain ⟨d, hd, z, hz, h⟩ := hD (s.θΓ x.out⁻¹) (by rwa [← s.comm, mul_assoc, ← map_mul])
  refine ⟨d, hd, ?_⟩
  have : s.θΓ.symm d = x.out⁻¹ * z⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_mul, h, s.fix _ (inv_mem hz), mul_inv_cancel_right]
  show (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
  rw [this, mul_inv_rev, inv_inv, inv_inv, ← Subgroup.mem_center_iff.1 (B.cenΓ hz), QuotientGroup.mk_mul_of_mem _ hz, QuotientGroup.out_eq']

/- English proof (translation)
The claim follows from `(f_fin hD g y).subset fun x hx h => hx (by simp only [Tk, h, zero_smul])`.
-/
theorem Tk_fin (hD : HD s f) (g y : G) : (Function.support fun x : Γ ⧸ B.Γ₀ => Tk s f g y x.out⁻¹).Finite :=
  (f_fin hD g y).subset fun x hx h => hx (by simp only [Tk, h, zero_smul])

variable (s f) in

noncomputable def Ek (g y : G) : Module.End ℂ V := ∑ᶠ x : Γ ⧸ B.Γ₀, Tk s f g y x.out⁻¹

/- English proof (translation)
Use `haveI := normal0 B`. Unfold `Ek`. Rewrite using `[mul_finsum' _ _ (Tk_fin hD g y), ← finsum_comp_equiv (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) (f := fun x => B.W γ * Tk s f g y x.out⁻¹)]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Establish `e : (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) x = ((x.out * s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)` using `by simp`.

Rewrite using `[e, Tk_out hf]`. Take `⟨γ, rfl⟩` from `s.θΓ.surjective γ`. Use extensionality with `v`. Simplify using `only [Tk, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.mul_apply, MulEquiv.symm_apply_apply, map_smul, ← s.int, ← s.comm]`. Rewrite using `[← Module.End.mul_apply (B.W γ), ← map_mul]`.

Simplify using `[mul_assoc]`.
-/
theorem Ek_left (hf : s.IsTest f) (hD : HD s f) (γ : Γ) (g y : G) : Ek s f (B.ι γ * g) y = B.W γ * Ek s f g y := by
  haveI := normal0 B
  unfold Ek
  rw [mul_finsum' _ _ (Tk_fin hD g y), ← finsum_comp_equiv (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) (f := fun x => B.W γ * Tk s f g y x.out⁻¹)]
  refine finsum_congr fun x => ?_
  have e : (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) x = ((x.out * s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀) := by simp
  rw [e, Tk_out hf]
  obtain ⟨γ, rfl⟩ := s.θΓ.surjective γ
  ext v
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.mul_apply, MulEquiv.symm_apply_apply, map_smul, ← s.int, ← s.comm]
  rw [← Module.End.mul_apply (B.W γ), ← map_mul]
  simp [mul_assoc]

/- English proof (translation)
Unfold `Ek`. Rewrite using `[smul_finsum' _ (Tk_fin hD g y)]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Use `hf.left u⁻¹ (g⁻¹ * s.θ (B.ι x.out⁻¹ * y))` as an intermediate fact. Simplify using `only [map_inv B.ω, inv_inv, InvMemClass.coe_inv] at this`.

Simplify using `only [Tk]`. Rewrite using `[mul_inv_rev, mul_assoc, this, smul_smul]`.
-/
theorem Ek_right (hf : s.IsTest f) (hD : HD s f) (u : B.U) (g y : G) : Ek s f (g * u) y = (B.ω u : ℂ) • Ek s f g y := by
  unfold Ek
  rw [smul_finsum' _ (Tk_fin hD g y)]
  refine finsum_congr fun x => ?_
  have := hf.left u⁻¹ (g⁻¹ * s.θ (B.ι x.out⁻¹ * y))
  simp only [map_inv B.ω, inv_inv, InvMemClass.coe_inv] at this
  simp only [Tk]
  rw [mul_inv_rev, mul_assoc, this, smul_smul]

/- English proof (translation)
Use `letI := act B`. Use `haveI := normal0 B`. Use `haveI := finQ B hB`. Use `haveI := formsFin _ _ _ B hB`. Use `letI := Fintype.ofFinite (orbitRel.Quotient Γ (G ⧸ B.U))`.

Set `n : orbitRel.Quotient Γ (G ⧸ B.U) → ℂ` to `fun o => (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹`. Set `A : (orbitRel.Quotient Γ (G ⧸ B.U) → V) →ₗ[ℂ] B.Forms` to `{ toFun := fun w => ⟨fun g => ∑ o, n o • Ek s f g o.out.out (w o), fun γ g => by simp [Ek_left hf hD], fun g u => by`. Simplify using `only [Ek_right hf hD, Finset.smul_sum, LinearMap.smul_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => smul_comm _ _ _⟩`. Use the proof step `map_add' := fun a b => Subtype.ext (funext fun g => by simp [Finset.sum_add_distrib])`.

Use the proof step `map_smul' := fun c a => Subtype.ext (funext fun g => by`. Simplify using `only [Pi.smul_apply, map_smul, RingHom.id_apply, Submodule.coe_smul, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => smul_comm _ _ _) }`. Set `ev : B.Forms →ₗ[ℂ] (orbitRel.Quotient Γ (G ⧸ B.U) → V)` to `(LinearMap.funLeft ℂ V fun o => o.out.out).comp B.Forms.subtype`. Establish `hR : s.R f = A ∘ₗ ev`.

Use extensionality with `φ g`. Rewrite using `[rSpec _ _ _ B s f hf]`. Set `k : G ⧸ B.U → V` to `fun y => f (g⁻¹ * s.θ y.out) • s.Θ (φ.1 y.out)`. Establish `wd : ∀ y : G, k y = f (g⁻¹ * s.θ y) • s.Θ (φ.1 y)` using `fun y => by`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul B.U y`.

Simplify using `only [k]`. Rewrite using `[hu, map_mul, ← mul_assoc, hf.right, φ.2.2, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `e : ∀ x : G ⧸ B.U, k (MulAction.toPerm (s.θ.symm g) x) = f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out))` using `fun x => by`. Establish `: (MulAction.toPerm (s.θ.symm g) x : G ⧸ B.U) = ((s.θ.symm g * x.out : G) : G ⧸ B.U)` using `by conv_lhs => rw [← x.out_eq]`.

Both sides reduce to the same expression. Rewrite using `[this, wd]`. Simplify using the standard rewrite rules. Establish `kf : (Function.support k).Finite`. Use `Set.Finite.of_preimage (f := MulAction.toPerm (s.θ.symm g)) (hf.fin.subset fun x hx h => hx ?_) (Equiv.surjective _)` and prove the remaining obligations.

Rewrite using `[e, h, zero_smul]`. Take `⟨t1, t2⟩` from `finsum_triv B.Γ₀ (triv0 B) k kf`. Take `⟨c1, c2⟩` from `countC B.Γ₀ B.Γ₀ (triv0 B) le_rfl (stab0 B hB) k (fun z hz y => by rw [triv0 B z hz]) t1`. Rewrite `c2` using `[t2, finsum_curry _ c1, finsum_eq_sum_of_fintype, ← finsum_comp_equiv (MulAction.toPerm (s.θ.symm g))]`. Simplify using `only [e] at c2`.

Use `c2.symm.trans (Finset.sum_congr rfl fun o _ => ?_)` and prove the remaining obligations. Use `show _ = n o • Ek s f g o.out.out (φ.1 o.out.out)`. Use `map_finsum (n o • LinearMap.applyₗ (R := ℂ) (M₂ := V) (φ.1 o.out.out)) (Tk_fin hD g o.out.out)` as an intermediate fact. Use `Eq.trans (finsum_congr fun x => ?_) this.symm` and prove the remaining obligations. Establish `e2 : x.out⁻¹ • o.out = ((B.ι x.out⁻¹ * o.out.out : G) : G ⧸ B.U)` using `by conv_lhs => rw [← o.out.out_eq]`.

Both sides reduce to the same expression. Rewrite using `[e2, wd, φ.2.1]`. Both sides reduce to the same expression. Rewrite using `[hR, LinearMap.trace_comp_comm', trace_blocks (fun o' o => n o • Ek s f o'.out.out o.out.out) _ fun w o' => rfl, finsum_eq_sum_of_fintype]`. Use `Finset.sum_congr rfl fun o _ => ?_` and prove the remaining obligations.

Conclude with `map_finsum (LinearMap.trace ℂ V ∘ₗ LinearMap.lsmul ℂ _ (n o)) (Tk_fin hD _ _) |>.trans (finsum_congr fun x => by simp [n])`.
-/
theorem traceA [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (hD : HD s f) : letI := act B
    LinearMap.trace ℂ B.Forms (s.R f) = ∑ᶠ o : orbitRel.Quotient Γ (G ⧸ B.U), ∑ᶠ x : Γ ⧸ B.Γ₀,
      (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹ * LinearMap.trace ℂ V (Tk s f o.out.out o.out.out x.out⁻¹) := by
  letI := act B
  haveI := normal0 B
  haveI := finQ B hB
  haveI := formsFin _ _ _ B hB
  letI := Fintype.ofFinite (orbitRel.Quotient Γ (G ⧸ B.U))
  let n : orbitRel.Quotient Γ (G ⧸ B.U) → ℂ := fun o => (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹
  let A : (orbitRel.Quotient Γ (G ⧸ B.U) → V) →ₗ[ℂ] B.Forms :=
    { toFun := fun w => ⟨fun g => ∑ o, n o • Ek s f g o.out.out (w o), fun γ g => by simp [Ek_left hf hD], fun g u => by
        simp only [Ek_right hf hD, Finset.smul_sum, LinearMap.smul_apply]; exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp [Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Submodule.coe_smul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _) }
  let ev : B.Forms →ₗ[ℂ] (orbitRel.Quotient Γ (G ⧸ B.U) → V) := (LinearMap.funLeft ℂ V fun o => o.out.out).comp B.Forms.subtype
  have hR : s.R f = A ∘ₗ ev := by
    ext φ g
    rw [rSpec _ _ _ B s f hf]
    let k : G ⧸ B.U → V := fun y => f (g⁻¹ * s.θ y.out) • s.Θ (φ.1 y.out)
    have wd : ∀ y : G, k y = f (g⁻¹ * s.θ y) • s.Θ (φ.1 y) := fun y => by
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U y
      simp only [k]
      rw [hu, map_mul, ← mul_assoc, hf.right, φ.2.2, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]; simp
    have e : ∀ x : G ⧸ B.U, k (MulAction.toPerm (s.θ.symm g) x) = f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := fun x => by
      have : (MulAction.toPerm (s.θ.symm g) x : G ⧸ B.U) = ((s.θ.symm g * x.out : G) : G ⧸ B.U) := by
        conv_lhs => rw [← x.out_eq]
        rfl
      rw [this, wd]; simp
    have kf : (Function.support k).Finite := by
      refine Set.Finite.of_preimage (f := MulAction.toPerm (s.θ.symm g)) (hf.fin.subset fun x hx h => hx ?_) (Equiv.surjective _)
      rw [e, h, zero_smul]
    obtain ⟨t1, t2⟩ := finsum_triv B.Γ₀ (triv0 B) k kf
    obtain ⟨c1, c2⟩ := countC B.Γ₀ B.Γ₀ (triv0 B) le_rfl (stab0 B hB) k (fun z hz y => by rw [triv0 B z hz]) t1
    rw [t2, finsum_curry _ c1, finsum_eq_sum_of_fintype, ← finsum_comp_equiv (MulAction.toPerm (s.θ.symm g))] at c2
    simp only [e] at c2
    refine c2.symm.trans (Finset.sum_congr rfl fun o _ => ?_)
    show _ = n o • Ek s f g o.out.out (φ.1 o.out.out)
    have := map_finsum (n o • LinearMap.applyₗ (R := ℂ) (M₂ := V) (φ.1 o.out.out)) (Tk_fin hD g o.out.out)
    refine Eq.trans (finsum_congr fun x => ?_) this.symm
    have e2 : x.out⁻¹ • o.out = ((B.ι x.out⁻¹ * o.out.out : G) : G ⧸ B.U) := by
      conv_lhs => rw [← o.out.out_eq]
      rfl
    rw [e2, wd, φ.2.1]
    rfl
  rw [hR, LinearMap.trace_comp_comm', trace_blocks (fun o' o => n o • Ek s f o'.out.out o.out.out) _ fun w o' => rfl, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  exact map_finsum (LinearMap.trace ℂ V ∘ₗ LinearMap.lsmul ℂ _ (n o)) (Tk_fin hD _ _) |>.trans (finsum_congr fun x => by simp [n])

end UpperTheory.V.Z.Sym.Tf
