import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

/- English proof (translation)
Use `⟨fun k hk x y hxy => ?_⟩` and prove the remaining obligations. Establish `hk' : (k : K) ≠ 0` using `Nat.cast_ne_zero.2 hk`. Establish `e : (k : K) • x = (k : K) • y`. Simplify `hxy` using `only [Nat.cast_smul_eq_nsmul]`. Conclude with `smul_right_injective V hk' e`.
-/
theorem isAddTorsionFree_of_module (K V : Type*) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] : IsAddTorsionFree V := by
  refine ⟨fun k hk x y hxy => ?_⟩
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk
  have e : (k : K) • x = (k : K) • y := by
    simpa only [Nat.cast_smul_eq_nsmul] using hxy
  exact smul_right_injective V hk' e

/- English proof (translation)
Establish `h2 : H.toIntSubmodule.FG`. Use `Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ ?_` and prove the remaining obligations. Establish `: H.toIntSubmodule.map φ.toIntLinearMap = (H.map φ).toIntSubmodule`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `(Submodule.fg_iff_addSubgroup_fg _).2 hH`. Conclude with `(Submodule.fg_iff_addSubgroup_fg _).1 h2`.
-/
theorem fg_of_fg_map_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {H : AddSubgroup A} (φ : A →+ B) (hφ : Function.Injective φ) (hH : (H.map φ).FG) : H.FG := by
  have h2 : H.toIntSubmodule.FG := by
    refine Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ ?_
    have : H.toIntSubmodule.map φ.toIntLinearMap = (H.map φ).toIntSubmodule := by
      ext x
      simp
    rw [this]
    exact (Submodule.fg_iff_addSubgroup_fg _).2 hH
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField E] in

/- English proof (translation)
Establish `hk : La.relIndex (dualLattice h La) • y ∈ La`. Use `AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩` as an intermediate fact. Conclude with `AddSubgroup.mem_addSubgroupOf.1 this`. Take `⟨c, hc⟩` from `Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le`. Rewrite using `[hc, mul_comm, ← smul_smul]`.

Conclude with `La.nsmul_mem hk c`.
-/
theorem factorial_nsmul_mem_of_mem_dual {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by
  have hk : La.relIndex (dualLattice h La) • y ∈ La := by
    have := AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩
    exact AddSubgroup.mem_addSubgroupOf.1 this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
  rw [hc, mul_comm, ← smul_smul]
  exact La.nsmul_mem hk c

/- English proof (translation)
Introduce `v₀ w₀ hvw h' hh' D n hn`. Use `⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩` and prove the remaining obligations. Introduce `La hLa hdec`. Use `set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP`. Take `⟨hvv, hww, hvw1⟩` from `hvw`.

Establish `hwv1 : h.toSesq w₀ v₀ = 1`. Rewrite using `[← h.isSymm.eq v₀ w₀, hvw1, map_one]`. Establish `hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0` using `fun x y hxy => by`. Rewrite using `[← h.isSymm.eq x y, hxy, map_zero]`. Establish `memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La` using `fun x => Iff.rfl`.

Set `π₀ : W →ₗ[E] W` to `LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀`. Establish `hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀` using `fun x => rfl`. Establish `hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀)`. Introduce `x`. Rewrite using `[hπ₀, mem_hypComplement]`.

Apply the tactic sequence `constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring`. Establish `hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y` using `fun y hy => by`. Rewrite `hy` using `[mem_hypComplement]`. Rewrite using `[hπ₀, hy.1, hy.2]`. Simplify using the standard rewrite rules.

Establish `hπv : π₀ v₀ = 0`. Rewrite using `[hπ₀, hwv1, hvv]`. Simplify using the standard rewrite rules. Establish `hπw : π₀ w₀ = 0`. Rewrite using `[hπ₀, hww, hvw1]`.

Simplify using the standard rewrite rules. Establish `hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧ n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧ n • π₀ x = n • x - a • v₀ - b • w₀`. Introduce `x hx`. Take `⟨a, ha, b, hb, hmem⟩` from `hdec x hx`. Express the relevant statement in the definitionally equal form `a • v₀ ∈ La at ha`.

Express the relevant statement in the definitionally equal form `b • w₀ ∈ La at hb`. Use `⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]`. Simplify using the standard rewrite rules. Establish `hPlat : IsLattice E P`.

Use `⟨fun a x hx => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[memP]`. Conclude with `hLa.isLattice.smul_mem a _ hx`. Use `fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_` and prove the remaining obligations. Conclude with `fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg`.

Set `π : W →ₗ[E] (hypComplement h v₀ w₀)` to `π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem`. Establish `hrange : LinearMap.range π = ⊤` using `LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩`. Rewrite using `[eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, b, -, -, -, hzLa, hkey⟩` from `hz x hx`.

Establish `hnE : (n : E) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `hnx : (n : E) • π x ∈ P`. Rewrite using `[memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]`. Express the relevant statement in the definitionally equal form `n • π₀ x ∈ La`. Rewrite using `[hkey]`.

Conclude with `hzLa`. Establish `: π x = (n : E)⁻¹ • ((n : E) • π x)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hnE, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hnx)`.

Establish `hPint : IsIntegralOn h' P` using `fun x hx y hy => by`. Rewrite using `[hh']`. Conclude with `hLa.integral _ hx _ hy`. Use `set N := D.factorial * n with hN`. Establish `hNpos : 0 < N` using `Nat.mul_pos (Nat.factorial_pos D) hn`.

Use `set G := dualLattice h' P with hG`. Establish `hPG : P ≤ G` using `fun x hx y hy => hPint x hx y hy`. Establish `hNG : G.map (nsmulAddMonoidHom N) ≤ P`. Introduce and unpack `_ ⟨y', hy', rfl⟩`. Establish `hdual : n • (y' : W) ∈ dualLattice h La`.

Introduce `x hx`. Take `⟨a, b, -, -, hmem, hzLa, -⟩` from `hz x hx`. Establish `hy0` using `(mem_hypComplement.1 y'.2)`. Establish `e1 : h.toSesq (y' : W) v₀ = 0` using `hsymm0 _ _ hy0.1`. Establish `e2 : h.toSesq (y' : W) w₀ = 0` using `hsymm0 _ _ hy0.2`.

Establish `hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀` using `by abel`. Establish `key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀)`. Rewrite using `[map_nsmul, LinearMap.smul_apply, ← map_nsmul]`. Use `conv_lhs => rw [hnx]`. Rewrite using `[map_add, map_add, map_smul, map_smul, e1, e2]`.

Simplify using the standard rewrite rules. Rewrite using `[key]`. Use `hy' ⟨_, hmem⟩ hzLa` as an intermediate fact. Rewrite `this` using `[hh']`. Then use the resulting hypothesis. Establish `h2` using `factorial_nsmul_mem_of_mem_dual hLa hdual`.

Rewrite using `[nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]`. Conclude with `h2`. Establish `: IsAddTorsionFree (hypComplement h v₀ w₀)` using `isAddTorsionFree_of_module E (hypComplement h v₀ w₀)`. Establish `hGfg : G.FG` using `fg_of_fg_map_of_injective (nsmulAddMonoidHom N) (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne') (fg_of_le_fg hNG hPlat.fg)`. Establish `: Module.Finite ℤ G.toIntSubmodule` using `Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)`.

Establish `: Module.Finite ℤ G` using `inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)`. Establish `hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W`. Use `letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)`. Establish `: IsScalarTower ℚ E W` using `⟨fun q e w => by`. Express the relevant statement in the definitionally equal form `(q • e) • w = algebraMap ℚ E q • e • w`.

Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `: Module.Finite ℚ W` using `Module.Finite.trans E W`. Set `b` to `Module.finBasis ℤ G`. Set `f : G →ₗ[ℤ] W` to `((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap`. Establish `hf : Function.Injective f` using `Subtype.val_injective.comp Subtype.val_injective`.

Establish `hliZ : LinearIndependent ℤ (f ∘ b)` using `b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)`. Establish `hliQ : LinearIndependent ℚ (f ∘ b)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ`. Use `hliQ.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W]`. Conclude with `this`.

Establish `hidx : P.relIndex G ≤ N ^ finrank ℤ G`. Rewrite using `[← AddSubgroup.relIndex_map_nsmul N G]`. Use `AddSubgroup.relIndex_le_of_le_left hNG ?_` and prove the remaining obligations. Rewrite using `[AddSubgroup.relIndex_map_nsmul]`. Check the signs of the components of the expression.

Use `⟨hPlat, hPint, fun h0 => ?_, ?_⟩` and prove the remaining obligations. Use `AddSubgroup.relIndex_eq_zero_of_le_left hNG h0` as an intermediate fact. Rewrite `this` using `[AddSubgroup.relIndex_map_nsmul]`. Conclude with `(pow_ne_zero _ hNpos.ne') this`. Conclude with `hidx.trans (Nat.pow_le_pow_right hNpos hrank)`.
-/
theorem ComplementLattice.proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by
  intro v₀ w₀ hvw h' hh' D n hn
  refine ⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩
  intro La hLa hdec
  set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP
  obtain ⟨hvv, hww, hvw1⟩ := hvw
  have hwv1 : h.toSesq w₀ v₀ = 1 := by
    rw [← h.isSymm.eq v₀ w₀, hvw1, map_one]
  have hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0 := fun x y hxy => by
    rw [← h.isSymm.eq x y, hxy, map_zero]
  have memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La := fun x => Iff.rfl

  let π₀ : W →ₗ[E] W :=
    LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀
  have hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀ := fun x => rfl
  have hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀) := by
    intro x
    rw [hπ₀, mem_hypComplement]
    constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring
  have hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y := fun y hy => by
    rw [mem_hypComplement] at hy
    rw [hπ₀, hy.1, hy.2]
    simp
  have hπv : π₀ v₀ = 0 := by
    rw [hπ₀, hwv1, hvv]
    simp
  have hπw : π₀ w₀ = 0 := by
    rw [hπ₀, hww, hvw1]
    simp

  have hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧
      n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧
      n • π₀ x = n • x - a • v₀ - b • w₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hmem⟩ := hdec x hx
    change a • v₀ ∈ La at ha
    change b • w₀ ∈ La at hb
    refine ⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩
    rw [← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]
    simp

  have hPlat : IsLattice E P := by
    refine ⟨fun a x hx => ?_, ?_, ?_⟩
    · rw [memP] at hx ⊢
      exact hLa.isLattice.smul_mem a _ hx
    · refine fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_
      exact fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg
    · let π : W →ₗ[E] (hypComplement h v₀ w₀) := π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem
      have hrange : LinearMap.range π = ⊤ :=
        LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩
      rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top,
        Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, b, -, -, -, hzLa, hkey⟩ := hz x hx
      have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hnx : (n : E) • π x ∈ P := by
        rw [memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
        change n • π₀ x ∈ La
        rw [hkey]
        exact hzLa
      have : π x = (n : E)⁻¹ • ((n : E) • π x) := by
        rw [smul_smul, inv_mul_cancel₀ hnE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)

  have hPint : IsIntegralOn h' P := fun x hx y hy => by
    rw [hh']
    exact hLa.integral _ hx _ hy
  set N := D.factorial * n with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.factorial_pos D) hn
  set G := dualLattice h' P with hG
  have hPG : P ≤ G := fun x hx y hy => hPint x hx y hy

  have hNG : G.map (nsmulAddMonoidHom N) ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have hdual : n • (y' : W) ∈ dualLattice h La := by
      intro x hx
      obtain ⟨a, b, -, -, hmem, hzLa, -⟩ := hz x hx
      have hy0 := (mem_hypComplement.1 y'.2)
      have e1 : h.toSesq (y' : W) v₀ = 0 := hsymm0 _ _ hy0.1
      have e2 : h.toSesq (y' : W) w₀ = 0 := hsymm0 _ _ hy0.2
      have hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀ := by abel
      have key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀) := by
        rw [map_nsmul, LinearMap.smul_apply, ← map_nsmul]
        conv_lhs => rw [hnx]
        rw [map_add, map_add, map_smul, map_smul, e1, e2]
        simp
      rw [key]
      have := hy' ⟨_, hmem⟩ hzLa
      rwa [hh'] at this
    have h2 := factorial_nsmul_mem_of_mem_dual hLa hdual
    rw [nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]
    exact h2

  have : IsAddTorsionFree (hypComplement h v₀ w₀) := isAddTorsionFree_of_module E (hypComplement h v₀ w₀)
  have hGfg : G.FG := fg_of_fg_map_of_injective (nsmulAddMonoidHom N)
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne')
    (fg_of_le_fg hNG hPlat.fg)
  have : Module.Finite ℤ G.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)
  have : Module.Finite ℤ G := inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)
  have hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W := by
    letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)
    have : IsScalarTower ℚ E W := ⟨fun q e w => by
      change (q • e) • w = algebraMap ℚ E q • e • w
      rw [Algebra.smul_def, mul_smul]⟩
    have : Module.Finite ℚ W := Module.Finite.trans E W
    let b := Module.finBasis ℤ G
    let f : G →ₗ[ℤ] W := ((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap
    have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hliZ : LinearIndependent ℤ (f ∘ b) :=
      b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
    have := hliQ.fintype_card_le_finrank
    rw [Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W] at this
    exact this
  have hidx : P.relIndex G ≤ N ^ finrank ℤ G := by
    rw [← AddSubgroup.relIndex_map_nsmul N G]
    refine AddSubgroup.relIndex_le_of_le_left hNG ?_
    rw [AddSubgroup.relIndex_map_nsmul]
    positivity
  refine ⟨hPlat, hPint, fun h0 => ?_, ?_⟩
  · have := AddSubgroup.relIndex_eq_zero_of_le_left hNG h0
    rw [AddSubgroup.relIndex_map_nsmul] at this
    exact (pow_ne_zero _ hNpos.ne') this
  · exact hidx.trans (Nat.pow_le_pow_right hNpos hrank)

end Complement

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
