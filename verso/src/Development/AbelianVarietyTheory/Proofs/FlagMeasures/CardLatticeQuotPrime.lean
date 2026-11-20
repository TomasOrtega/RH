import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

/- English proof (translation)
Establish `: IsArtinianRing (R ⧸ I)` using `isArtinian_of_finite`. Take `⟨b⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N) (fun P => by`. Use `P.isMaximal` as an intermediate fact. Set `: Field ((R ⧸ I) ⧸ P.asIdeal)` to `Ideal.Quotient.field _`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥`. Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]`. Conclude with `h1)`. Rewrite using `[← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]`.
-/
theorem card_quot_smul_top_of_flat {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

def inclLat (I : AutInst) : I.L →+ I.Lf where
  toFun x := ⟨fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x.1 i), incl_mem_lamAf I.L x.2⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' x y := Subtype.ext (funext fun i => map_add _ (x.1 i) (y.1 i))

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun i => map_mul (Formalism.UG.inclE (F := I.F) (Af I.F)) (a : I.E) (x.1 i))`.
-/
theorem inclLat_smul (I : AutInst) (a : 𝓞 I.E) (x : I.L) :
    inclLat I (a • x) = Inhab.psi I.F I.E a • inclLat I x :=
  Subtype.ext (funext fun i => map_mul (Formalism.UG.inclE (F := I.F) (Af I.F)) (a : I.E) (x.1 i))

/- English proof (translation)
Take `⟨x, hx, z, hz, e⟩` from `exists_approx I.L p (Nat.one_le_iff_ne_zero.2 hp) y.1 y.2`. Use `⟨⟨x, hx⟩, ⟨z, hz⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use function extensionality and compare the values at `i`. Use `show _ + (p : I.E ⊗[I.F] Af I.F) * z i = _ + ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z i`.

Rewrite using `[Subring.coe_natCast]`. Both sides reduce to the same expression.
-/
theorem exists_inclLat_add (I : AutInst) {p : ℕ} (hp : p ≠ 0) (y : I.Lf) :
    ∃ (x : I.L) (z : I.Lf), y = inclLat I x + (p : IntAf I.F I.E) • z := by
  obtain ⟨x, hx, z, hz, e⟩ := exists_approx I.L p (Nat.one_le_iff_ne_zero.2 hp) y.1 y.2
  refine ⟨⟨x, hx⟩, ⟨z, hz⟩, Subtype.ext ?_⟩
  rw [e]
  funext i
  show _ + (p : I.E ⊗[I.F] Af I.F) * z i = _ + ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z i
  rw [Subring.coe_natCast]
  rfl

/- English proof (translation)
Establish `hpE : (p : I.E) ≠ 0` using `by exact_mod_cast hp`. Establish `hz : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (((p : I.E)⁻¹ • x.1) i)) = z.1 := by`. Use function extensionality and compare the values at `i`. Establish `hi : Formalism.UG.inclE (F` using `I.F) (Af I.F) (x.1 i) = ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z.1 i := congrFun (congrArg Subtype.val h) i`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, hi, Subring.coe_natCast, ← map_natCast (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) p, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpE, map_one, one_mul]`.

Use `⟨⟨_, (incl_mem_iff (F := I.F) I.L I.L_fg I.L_span ((p : I.E)⁻¹ • x.1)).1 (hz ▸ z.2)⟩, Subtype.ext (funext fun i => ?_)⟩` and prove the remaining obligations. Use `show x.1 i = algebraMap (𝓞 I.E) I.E (p : 𝓞 I.E) * ((p : I.E)⁻¹ * x.1 i)`. Rewrite using `[map_natCast, mul_inv_cancel_left₀ hpE]`.
-/
theorem exists_eq_smul_of_inclLat (I : AutInst) {p : ℕ} (hp : p ≠ 0) (x : I.L) (z : I.Lf)
    (h : inclLat I x = (p : IntAf I.F I.E) • z) : ∃ u : I.L, x = (p : 𝓞 I.E) • u := by
  have hpE : (p : I.E) ≠ 0 := by exact_mod_cast hp
  have hz : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((p : I.E)⁻¹ • x.1) i)) = z.1 := by
    funext i
    have hi : Formalism.UG.inclE (F := I.F) (Af I.F) (x.1 i) =
        ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z.1 i := congrFun (congrArg Subtype.val h) i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hi, Subring.coe_natCast,
      ← map_natCast (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) p, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hpE, map_one, one_mul]
  refine ⟨⟨_, (incl_mem_iff (F := I.F) I.L I.L_fg I.L_span ((p : I.E)⁻¹ • x.1)).1 (hz ▸ z.2)⟩,
    Subtype.ext (funext fun i => ?_)⟩
  show x.1 i = algebraMap (𝓞 I.E) I.E (p : 𝓞 I.E) * ((p : I.E)⁻¹ * x.1 i)
  rw [map_natCast, mul_inv_cancel_left₀ hpE]

/- English proof (translation)
Establish `hpe : (p : S) ∈ 𝔟` using `by simpa using hab _ hpa`. Set `φ : M →+ N ⧸ (𝔟 • ⊤ : Submodule S N)` to `(𝔟 • ⊤ : Submodule S N).mkQ.toAddMonoidHom.comp ι`. Establish `hφ : ∀ x, φ x = Submodule.Quotient.mk (ι x)` using `fun _ => rfl`. Establish `hsurj : Function.Surjective φ`. Introduce `q`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨x, z, rfl⟩` from `hd y`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, eq_comm, Submodule.Quotient.eq, add_sub_cancel_left]`. Conclude with `Submodule.smul_mem_smul hpe Submodule.mem_top`.

Establish `hdec : ∀ y ∈ (𝔟 • ⊤ : Submodule S N), ∃ x ∈ (𝔞 • ⊤ : Submodule R M), ∃ z : N, y = ι x + (p : S) • z`. Introduce `y hy`. Use `Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)` and prove the remaining obligations. Take `⟨b, hb, t, e⟩` from `hba a ha`. Take `⟨x, z, rfl⟩` from `hd y`.

Use `⟨b • x, Submodule.smul_mem_smul hb Submodule.mem_top, t • ι x + a • z, ?_⟩` and prove the remaining obligations. Rewrite using `[hι, smul_add, smul_add, smul_comm a, ← add_assoc, smul_smul _ t, ← add_smul, ← e]`. Take `⟨x, hx, z, rfl⟩` from `hy`. Take `⟨x', hx', z', rfl⟩` from `hy'`. Use `⟨x + x', add_mem hx hx', z + z', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hker : (𝔞 • ⊤ : Submodule R M).toAddSubgroup = φ.ker`. Use `AddSubgroup.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_toAddSubgroup]`.

Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `Submodule.smul_induction_on h (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)` and prove the remaining obligations. Rewrite using `[hι]`. Conclude with `Submodule.smul_mem_smul (hab a ha) Submodule.mem_top`. Rewrite using `[map_add]`.

Conclude with `add_mem hy hy'`. Take `⟨x', hx', z, e⟩` from `hdec _ h`. Take `⟨u, hu⟩` from `hi (x - x') z (by rw [map_sub, e, add_sub_cancel_left])`. Rewrite using `[← sub_add_cancel x x', hu]`. Conclude with `add_mem (Submodule.smul_mem_smul hpa Submodule.mem_top) hx'`.

Establish `e : (M ⧸ (𝔞 • ⊤ : Submodule R M).toAddSubgroup) ≃ (N ⧸ (𝔟 • ⊤ : Submodule S N))` using `((QuotientAddGroup.quotientAddEquivOfEq hker).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)).toEquiv`. Conclude with `(Nat.card_congr e).symm`.
-/
theorem card_quot_eq_of_dense {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (ψ : R →+* S) (ι : M →+ N) (hι : ∀ a x, ι (a • x) = ψ a • ι x) (p : ℕ)
    (𝔞 : Ideal R) (𝔟 : Ideal S) (hpa : (p : R) ∈ 𝔞) (hab : ∀ a ∈ 𝔞, ψ a ∈ 𝔟)
    (hba : ∀ s ∈ 𝔟, ∃ a ∈ 𝔞, ∃ t : S, s = ψ a + (p : S) * t)
    (hd : ∀ y : N, ∃ (x : M) (z : N), y = ι x + (p : S) • z)
    (hi : ∀ (x : M) (z : N), ι x = (p : S) • z → ∃ u : M, x = (p : R) • u) :
    Nat.card (N ⧸ (𝔟 • ⊤ : Submodule S N)) = Nat.card (M ⧸ (𝔞 • ⊤ : Submodule R M)) := by
  have hpe : (p : S) ∈ 𝔟 := by simpa using hab _ hpa
  let φ : M →+ N ⧸ (𝔟 • ⊤ : Submodule S N) := (𝔟 • ⊤ : Submodule S N).mkQ.toAddMonoidHom.comp ι
  have hφ : ∀ x, φ x = Submodule.Quotient.mk (ι x) := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, z, rfl⟩ := hd y
    refine ⟨x, ?_⟩
    rw [hφ, eq_comm, Submodule.Quotient.eq, add_sub_cancel_left]
    exact Submodule.smul_mem_smul hpe Submodule.mem_top
  have hdec : ∀ y ∈ (𝔟 • ⊤ : Submodule S N), ∃ x ∈ (𝔞 • ⊤ : Submodule R M), ∃ z : N,
      y = ι x + (p : S) • z := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
    · obtain ⟨b, hb, t, e⟩ := hba a ha
      obtain ⟨x, z, rfl⟩ := hd y
      refine ⟨b • x, Submodule.smul_mem_smul hb Submodule.mem_top, t • ι x + a • z, ?_⟩
      rw [hι, smul_add, smul_add, smul_comm a, ← add_assoc, smul_smul _ t, ← add_smul, ← e]
    · obtain ⟨x, hx, z, rfl⟩ := hy
      obtain ⟨x', hx', z', rfl⟩ := hy'
      refine ⟨x + x', add_mem hx hx', z + z', ?_⟩
      rw [map_add, smul_add]
      abel
  have hker : (𝔞 • ⊤ : Submodule R M).toAddSubgroup = φ.ker := by
    refine AddSubgroup.ext fun x => ?_
    rw [AddMonoidHom.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_toAddSubgroup]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine Submodule.smul_induction_on h (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
      · rw [hι]
        exact Submodule.smul_mem_smul (hab a ha) Submodule.mem_top
      · rw [map_add]
        exact add_mem hy hy'
    · obtain ⟨x', hx', z, e⟩ := hdec _ h
      obtain ⟨u, hu⟩ := hi (x - x') z (by rw [map_sub, e, add_sub_cancel_left])
      rw [← sub_add_cancel x x', hu]
      exact add_mem (Submodule.smul_mem_smul hpa Submodule.mem_top) hx'
  have e : (M ⧸ (𝔞 • ⊤ : Submodule R M).toAddSubgroup) ≃ (N ⧸ (𝔟 • ⊤ : Submodule S N)) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)).toEquiv
  exact (Nat.card_congr e).symm

/- English proof (translation)
Establish `: IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype`. Use `⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩` and prove the remaining obligations. Use `isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s`. Establish `hy : y ∈ Submodule.span K (p : Set V)` using `h ▸ Submodule.mem_top`.

Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, ht⟩, t), rfl⟩`. Rewrite using `[← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl, IsFractionRing.finrank_right_eq (𝓞 K) K V]`.
-/
theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

/- English proof (translation)
Rewrite using `[finrank_of_span_top I.L I.L_span, Module.finrank_fin_fun]`.
-/
theorem finrank_lattice (I : AutInst) : Module.finrank (𝓞 I.E) I.L = I.n := by
  rw [finrank_of_span_top I.L I.L_span, Module.finrank_fin_fun]

/- English proof (translation)
Introduce `I p w hp hw`. Take `⟨r, hr⟩` from `Inhab.exists_reduction (F := I.F) p hp w hw`. Establish `hk` using `Inhab.ker_eq_extId hp.ne_zero r hr`. Establish `hpw : (p : 𝓞 I.E) ∈ w.asIdeal` using `(hr _).1 (by rw [map_natCast, map_natCast, ZMod.natCast_self])`. Establish `hab : ∀ a ∈ w.asIdeal, Inhab.psi I.F I.E a ∈ extId I w.asIdeal` using `fun a ha => Ideal.subset_span ⟨a, ha, rfl⟩`.

Establish `hba : ∀ s ∈ extId I w.asIdeal, ∃ a ∈ w.asIdeal, ∃ t : IntAf I.F I.E, s = Inhab.psi I.F I.E a + (p : IntAf I.F I.E) * t`. Introduce `s hs`. Take `⟨b, t, e⟩` from `Inhab.exists_approx hp.ne_zero s`. Use `⟨b, (hr b).1 ?_, t, e⟩` and prove the remaining obligations. Establish `h0 : r s = 0` using `(RingHom.mem_ker).1 (hk.ge hs)`.

Rewrite `h0` using `[e, r.map_add, r.map_mul, map_natCast r p, ZMod.natCast_self, zero_mul, add_zero]`. Conclude with `h0`. Use `(card_quot_eq_of_dense (Inhab.psi I.F I.E) (inclLat I) (inclLat_smul I) p w.asIdeal (extId I w.asIdeal) hpw hab hba (exists_inclLat_add I hp.ne_zero) (exists_eq_smul_of_inclLat I hp.ne_zero)).trans ?_` and prove the remaining obligations. Establish `hfin : Finite (𝓞 I.E ⧸ w.asIdeal)` using `(Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)`. Establish `: Module.Finite (𝓞 I.E) I.L` using `Module.Finite.iff_fg.2 I.L_fg`.

Establish `h` using `card_quot_smul_top_of_flat (N := I.L) w.asIdeal`. Rewrite `h` using `[finrank_lattice, ← Submodule.cardQuot_apply w.asIdeal, ← Ideal.absNorm_apply, hw]`. Conclude with `h`.
-/
theorem card_quot_extId : ∀ (I : AutInst) (p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), p.Prime → Ideal.absNorm w.asIdeal = p → Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ I.n := by
  intro I p w hp hw
  obtain ⟨r, hr⟩ := Inhab.exists_reduction (F := I.F) p hp w hw
  have hk := Inhab.ker_eq_extId hp.ne_zero r hr
  have hpw : (p : 𝓞 I.E) ∈ w.asIdeal := (hr _).1 (by rw [map_natCast, map_natCast, ZMod.natCast_self])
  have hab : ∀ a ∈ w.asIdeal, Inhab.psi I.F I.E a ∈ extId I w.asIdeal :=
    fun a ha => Ideal.subset_span ⟨a, ha, rfl⟩
  have hba : ∀ s ∈ extId I w.asIdeal, ∃ a ∈ w.asIdeal, ∃ t : IntAf I.F I.E,
      s = Inhab.psi I.F I.E a + (p : IntAf I.F I.E) * t := by
    intro s hs
    obtain ⟨b, t, e⟩ := Inhab.exists_approx hp.ne_zero s
    refine ⟨b, (hr b).1 ?_, t, e⟩
    have h0 : r s = 0 := (RingHom.mem_ker).1 (hk.ge hs)
    rw [e, r.map_add, r.map_mul, map_natCast r p, ZMod.natCast_self, zero_mul, add_zero] at h0
    exact h0
  refine (card_quot_eq_of_dense (Inhab.psi I.F I.E) (inclLat I) (inclLat_smul I) p w.asIdeal
    (extId I w.asIdeal) hpw hab hba (exists_inclLat_add I hp.ne_zero)
    (exists_eq_smul_of_inclLat I hp.ne_zero)).trans ?_
  have hfin : Finite (𝓞 I.E ⧸ w.asIdeal) := (Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)
  have : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  have h := card_quot_smul_top_of_flat (N := I.L) w.asIdeal
  rw [finrank_lattice, ← Submodule.cardQuot_apply w.asIdeal, ← Ideal.absNorm_apply, hw] at h
  exact h

end GlobalTheory.AdelicLattice
