import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.FreeNear

section Abstract

variable {o A G B : Type} [CommRing o] [IsDomain o] [Ring A] [Algebra o A] [AddCommGroup G] [Fintype G]
  [AddCommGroup B]

/- English proof (translation)
Establish `h` using `AddChar.sum_eq_ite (ψ.compAddMonoidHom c)`. Simplify using `only [AddChar.compAddMonoidHom_apply] at h`. Rewrite using `[h]`. Use `if_congr ⟨fun h0 => ?_, fun h0 => ?_⟩ rfl rfl` and prove the remaining obligations. Use extensionality with `t`.

Conclude with `hψ _ (by simpa using DFunLike.congr_fun h0 t)`. Use extensionality with `t`. Simplify using `[h0]`.
-/
theorem sum_char_comp (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (c : G →+ B) :
    ∑ t, ψ (c t) = if c = 0 then (Fintype.card G : o) else 0 := by
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom c)
  simp only [AddChar.compAddMonoidHom_apply] at h
  rw [h]
  refine if_congr ⟨fun h0 => ?_, fun h0 => ?_⟩ rfl rfl
  · ext t
    exact hψ _ (by simpa using DFunLike.congr_fun h0 t)
  · ext t
    simp [h0]

/- English proof (translation)
Establish `h1 : (∑ t, ψ (-(c t)) • ρ t) * (∑ t, ψ (-(c' t)) • ρ t) = (∑ s, ψ ((c' - c) s)) • ∑ t, ψ (-(c' t)) • ρ t`. Rewrite using `[Finset.sum_mul, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.addLeft s) _ _ fun t => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm, hρ, smul_smul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Simplify using `only [AddMonoidHom.sub_apply, Equiv.coe_addLeft, map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[smul_mul_smul_comm, h1, sum_char_comp ψ hψ, smul_smul]`.

Distinguish the cases in `h : c = c'`. Substitute `h` using the available equality. Rewrite using `[if_pos (sub_self c), if_pos rfl, _root_.mul_assoc, hu, _root_.mul_one]`. Rewrite using `[if_neg (fun h0 => h (sub_eq_zero.1 h0).symm), if_neg h, mul_zero, zero_smul]`.
-/
theorem avg_mul_avg [DecidableEq (G →+ B)] (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (ρ : G → A)
    (hρ : ∀ a b, ρ a * ρ b = ρ (a + b)) (u : o) (hu : u * (Fintype.card G : o) = 1) (c c' : G →+ B) :
    (u • ∑ t, ψ (-(c t)) • ρ t) * (u • ∑ t, ψ (-(c' t)) • ρ t) =
      if c = c' then u • ∑ t, ψ (-(c t)) • ρ t else 0 := by
  have h1 : (∑ t, ψ (-(c t)) • ρ t) * (∑ t, ψ (-(c' t)) • ρ t) =
      (∑ s, ψ ((c' - c) s)) • ∑ t, ψ (-(c' t)) • ρ t := by
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun t => ?_
    rw [smul_mul_smul_comm, hρ, smul_smul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [AddMonoidHom.sub_apply, Equiv.coe_addLeft, map_add]
    abel
  rw [smul_mul_smul_comm, h1, sum_char_comp ψ hψ, smul_smul]
  by_cases h : c = c'
  · subst h
    rw [if_pos (sub_self c), if_pos rfl, _root_.mul_assoc, hu, _root_.mul_one]
  · rw [if_neg (fun h0 => h (sub_eq_zero.1 h0).symm), if_neg h, mul_zero, zero_smul]

/- English proof (translation)
Establish `h1 : ∀ t, (∑ c : G →+ B, ψ (-(c t))) • ρ t = (∑ c : G →+ B, ψ (-(c t))) • (1 : A)`. Introduce `t`. Distinguish the cases in `h : ∀ c : G →+ B, c t = 0`. Rewrite using `[hρ t h]`. Establish `h2` using `sum_char_comp ψ hψ (-(AddMonoidHom.eval (M := G) (N := B) t))`.

Rewrite `h2` using `[if_neg (fun h0 => h fun c => by simpa using DFunLike.congr_fun h0 c)]`. Simplify using `only [AddMonoidHom.neg_apply, AddMonoidHom.eval_apply_apply] at h2`. Rewrite using `[h2, zero_smul, zero_smul]`. Establish `h3 : ∀ c : G →+ B, ∑ t, ψ (-(c t)) = if c = 0 then (Fintype.card G : o) else 0`. Introduce `c`.

Simplify using `using sum_char_comp ψ hψ (-c)`. Rewrite using `[← Finset.smul_sum, Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, h1]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[smul_smul, hu, one_smul]`.
-/
theorem sum_avg [Fintype (G →+ B)] (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (ρ : G → A)
    (hρ : ∀ t, (∀ c : G →+ B, c t = 0) → ρ t = 1) (u : o) (hu : u * (Fintype.card G : o) = 1) :
    ∑ c : G →+ B, u • ∑ t, ψ (-(c t)) • ρ t = 1 := by
  have h1 : ∀ t, (∑ c : G →+ B, ψ (-(c t))) • ρ t = (∑ c : G →+ B, ψ (-(c t))) • (1 : A) := by
    intro t
    by_cases h : ∀ c : G →+ B, c t = 0
    · rw [hρ t h]
    · have h2 := sum_char_comp ψ hψ (-(AddMonoidHom.eval (M := G) (N := B) t))
      rw [if_neg (fun h0 => h fun c => by simpa using DFunLike.congr_fun h0 c)] at h2
      simp only [AddMonoidHom.neg_apply, AddMonoidHom.eval_apply_apply] at h2
      rw [h2, zero_smul, zero_smul]
  have h3 : ∀ c : G →+ B, ∑ t, ψ (-(c t)) = if c = 0 then (Fintype.card G : o) else 0 := by
    intro c
    simpa using sum_char_comp ψ hψ (-c)
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, h1]
  rw [Finset.sum_comm]
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, hu, one_smul]

end Abstract

section System

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance neZero_N : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance neZero_rN : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne _)⟩

/- English proof (translation)
The claim follows from `S.prim.pow (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))) (by ring)`.
-/
theorem isPrimitiveRoot_ζN : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))) (by ring)

/- English proof (translation)
The claim follows from `Finite.of_injective _ DFunLike.coe_injective`.
-/
theorem finite_char (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) :=
  Finite.of_injective _ DFunLike.coe_injective

/- English proof (translation)
Take `⟨hiso, d, ⟨φ⟩⟩` from `hT`. Use `haveI := Fintype.ofFinite T`. Establish `hprim` using `isPrimitiveRoot_ζN S`. Set `ψ : AddChar (ZMod S.N) o` to `AddChar.zmodChar S.N hprim.pow_eq_one`. Establish `hψ : ∀ a, ψ a = 1 → a = 0` using `fun a ha => by`.

Rewrite `ha` using `[AddChar.zmodChar_apply, hprim.pow_eq_one_iff_dvd]`. Conclude with `(ZMod.val_eq_zero a).1 (Nat.eq_zero_of_dvd_of_lt ha a.val_lt)`. Establish `hunit : IsUnit (Nat.card T : o)`. Rewrite using `[Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]`. Conclude with `S.unit.pow _`.

Establish `hu : Ring.inverse (Nat.card T : o) * (Fintype.card T : o) = 1`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `Ring.inverse_mul_cancel _ hunit`. Establish `hp : ∀ c, S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, ψ (-(c t)) • S.ρ t` using `fun c => by`. Rewrite using `[ThetaSys.proj, finsum_eq_sum_of_fintype]`.

Both sides reduce to the same expression. Simplify using `only [hp]`. Use `⟨avg_mul_avg ψ hψ (fun t : T => S.ρ t) (fun a b => S.ρ_add _ _ ?_) _ hu, sum_avg ψ hψ (fun t : T => S.ρ t) (fun t ht => S.ρ_one _ ?_) _ hu⟩` and prove the remaining obligations. Rewrite using `[hiso a.2 b b.2, smul_zero]`. Establish `h : S.r • t = 0`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_nsmul, map_zero]`. Use function extensionality and compare the values at `i`. Establish `h1` using `ht (((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ => ZMod (S.r * S.N)) i)).comp φ.toAddMonoidHom)`. Express the relevant statement in the definitionally equal form `ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (φ t i) = 0 at h1`.

Express the relevant statement in the definitionally equal form `S.r • φ t i = 0`. Take `⟨n, hn⟩` from `ZMod.natCast_zmod_surjective (φ t i)`. Rewrite `h1` using `[← hn, map_natCast, ZMod.natCast_eq_zero_iff]`. Rewrite using `[← hn, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Conclude with `Nat.mul_dvd_mul_left _ h1`.

Conclude with `congrArg Subtype.val h`.
-/
theorem proj_orthogonal [IsDomain o] (T : AddSubgroup S.Gam) (hT : S.IsoFree T) [Fintype (T →+ ZMod S.N)]
    [DecidableEq (T →+ ZMod S.N)] :
    (∀ c c', S.proj T c * S.proj T c' = if c = c' then S.proj T c else 0) ∧ ∑ c, S.proj T c = 1 := by
  obtain ⟨hiso, d, ⟨φ⟩⟩ := hT
  haveI := Fintype.ofFinite T
  have hprim := isPrimitiveRoot_ζN S
  let ψ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hprim.pow_eq_one
  have hψ : ∀ a, ψ a = 1 → a = 0 := fun a ha => by
    rw [AddChar.zmodChar_apply, hprim.pow_eq_one_iff_dvd] at ha
    exact (ZMod.val_eq_zero a).1 (Nat.eq_zero_of_dvd_of_lt ha a.val_lt)
  have hunit : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have hu : Ring.inverse (Nat.card T : o) * (Fintype.card T : o) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Ring.inverse_mul_cancel _ hunit
  have hp : ∀ c, S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, ψ (-(c t)) • S.ρ t := fun c => by
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype]
    rfl
  simp only [hp]
  refine ⟨avg_mul_avg ψ hψ (fun t : T => S.ρ t) (fun a b => S.ρ_add _ _ ?_) _ hu,
    sum_avg ψ hψ (fun t : T => S.ρ t) (fun t ht => S.ρ_one _ ?_) _ hu⟩
  · rw [hiso a.2 b b.2, smul_zero]
  · have h : S.r • t = 0 := by
      apply φ.injective
      rw [map_nsmul, map_zero]
      funext i
      have h1 := ht (((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun _ => ZMod (S.r * S.N)) i)).comp φ.toAddMonoidHom)
      change ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (φ t i) = 0 at h1
      change S.r • φ t i = 0
      obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (φ t i)
      rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
      rw [← hn, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact Nat.mul_dvd_mul_left _ h1
    exact congrArg Subtype.val h

end System

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

/- English proof (translation)
Use `isOpen_iff_forall_mem_open.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Use `⟨⋂ i, {w | (a i : Ω) ∈ M.O w}, fun w hw => ?_, isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _, Set.mem_iInter.2 fun i => (a i).2⟩` and prove the remaining obligations. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨a i, Set.mem_iInter.1 hw i⟩, rfl⟩`.
-/
theorem isOpen_setOf_mem_span {J I : Type} [Fintype I] (b : I → J → Ω) (v : J → Ω) :
    IsOpen {x : M.Z | v ∈ Submodule.span (M.O x) (Set.range b)} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine ⟨⋂ i, {w | (a i : Ω) ∈ M.O w}, fun w hw => ?_,
    isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _, Set.mem_iInter.2 fun i => (a i).2⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨a i, Set.mem_iInter.1 hw i⟩, rfl⟩

/- English proof (translation)
Use `⟨⟨⋂ v ∈ V, {x : M.Z | v ∈ Submodule.span (M.O x) (Set.range b)}, hV.isOpen_biInter fun v _ => isOpen_setOf_mem_span M b v⟩, Set.mem_iInter₂.2 hz, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `le_antisymm (Submodule.span_le.2 fun v hv => Set.mem_iInter₂.1 hx v hv) (Submodule.span_mono hb)`.
-/
theorem exists_opens_span_eq {J I : Type} [Fintype I] (b : I → J → Ω) (V : Set (J → Ω)) (hV : V.Finite)
    (hb : Set.range b ⊆ V) (z : M.Z) (hz : ∀ v ∈ V, v ∈ Submodule.span (M.O z) (Set.range b)) :
    ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W, Submodule.span (M.O x) V = Submodule.span (M.O x) (Set.range b) := by
  refine ⟨⟨⋂ v ∈ V, {x : M.Z | v ∈ Submodule.span (M.O x) (Set.range b)},
    hV.isOpen_biInter fun v _ => isOpen_setOf_mem_span M b v⟩, Set.mem_iInter₂.2 hz, fun x hx => ?_⟩
  exact le_antisymm (Submodule.span_le.2 fun v hv => Set.mem_iInter₂.1 hx v hv) (Submodule.span_mono hb)

end Model

end GlobalTheory.ZH.FreeNear

namespace GlobalTheory.ZH

open FreeNear in

/- English proof (translation)
Introduce `o Ω _ _ _ hA S M U₀ hAdm h0 hne z`. Use `haveI : IsDomain o := hA.inj.isDomain`. Establish `hT` using `(h0.1 z).1`. Use `haveI := finite_char S (S.TT M z)`. Use `haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)`.

Take `⟨hmul, hsum⟩` from `proj_orthogonal S _ hT`. Take `⟨x₁, hx₁⟩` from `hAdm.1.div z`. Use `choose k₁ hk₁ using fun c => hAdm.2 _ c hT (hne z c) z`. Take `⟨κ, col, hdet, hspan⟩` from `exists_basis_adapted_to_idempotents (M.O z) S.J (S.TT M z →+ ZMod S.N) (fun c => (algebraMap o (M.O z)).mapMatrix (S.proj _ c)) (fun c c' => by`. Rewrite using `[← map_mul, hmul]`.

Apply the tactic sequence `split_ifs <;> simp)`. Use the proof step `(by rw [← map_sum, hsum, map_one])`. Set `f : (S.TT M z →+ ZMod S.N) → Ω` to `fun c => S.th x₁ / S.FF _ c (k₁ c)`. Establish `hf : ∀ c, f c ≠ 0` using `fun c => div_ne_zero hx₁.1 (hk₁ c).1`. Set `b : Matrix S.J S.J Ω` to `Matrix.of fun i j => f (κ i) * algebraMap o Ω (S.proj _ (κ i) j (col i))`.

Establish `hb : b.det ≠ 0`. Establish `h1` using `(hdet.map (algebraMap (M.O z) Ω)).ne_zero`. Rewrite `h1` using `[RingHom.map_det]`. Establish `h2` using `Matrix.det_mul_column (fun i => f (κ i)) (Matrix.of fun i j => algebraMap o Ω (S.proj _ (κ i) j (col i)))`. Express the relevant statement in the definitionally equal form `b.det = _ at h2`.

Rewrite using `[h2]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hf _) h1`. It suffices to establish `h : ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W, _ = Submodule.span (M.O x) (Set.range b) by`. Take `⟨W, hz, hW⟩` from `h`. Conclude with `⟨b, W, hz, hb, hW⟩`.

Use `exists_opens_span_eq M b _ ?_ ?_ z ?_` and prove the remaining obligations. Use `(Set.finite_range fun q : (S.TT M z →+ ZMod S.N) × (S.J × (S.TT M z → ZMod ((S.r * S.N) ^ 2))) × S.Gam × S.J => fun j => S.th q.2.2.1 / S.FF _ q.1 q.2.1 * algebraMap o Ω (S.proj _ q.1 j q.2.2.2)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, k, x₀, i, -, -, rfl⟩`. Conclude with `⟨(c, k, x₀, i), rfl⟩`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `⟨κ i, k₁ _, x₁, col i, hk₁ _, hx₁, rfl⟩`. Introduce and unpack `_ ⟨c, k, x₀, i, hk, -, rfl⟩`. Establish `h1 : ∀ w ∈ Submodule.span (M.O z) {v : S.J → M.O z | ∃ i, κ i = c ∧ v = fun j => (algebraMap o (M.O z)).mapMatrix (S.proj _ c) j (col i)}, (fun j => f c * (w j : Ω)) ∈ Submodule.span (M.O z) (Set.range b)`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem _ h'`. Take `⟨i', rfl, rfl⟩` from `h'`. Conclude with `Submodule.subset_span ⟨i', rfl⟩`. Consider the case `zero`. Use `Submodule.zero_mem (Submodule.span (M.O z) (Set.range b)) using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Consider the case `add a a' _ _ ha ha'`. Use `Submodule.add_mem _ ha ha' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Simplify using `[mul_add]`. Consider the case `smul s a _ ha`. Use `Submodule.smul_mem _ s ha using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `[Subalgebra.smul_def, mul_left_comm]`.

Establish `h2` using `h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))`. Use `Submodule.smul_mem _ (⟨_, mul_mem (hx₁.2 x₀) (hk.2 (k₁ c))⟩ : M.O z) h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Use `hx₁.1` as an intermediate fact. Use `(hk₁ c).1` as an intermediate fact.

Express the relevant statement in the definitionally equal form `_ = S.th x₀ / S.th x₁ * (S.FF _ c (k₁ c) / S.FF _ c k) * (S.th x₁ / S.FF _ c (k₁ c) * algebraMap o Ω (S.proj _ c j i))`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_basis_lattice_near :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, ∃ (b : Matrix S.J S.J Ω) (W : M.Z.Opens), z ∈ W ∧ b.det ≠ 0 ∧ ∀ x ∈ W, Submodule.span (M.O x) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O x) (Set.range b)) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne z
  haveI : IsDomain o := hA.inj.isDomain
  have hT := (h0.1 z).1
  haveI := finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := proj_orthogonal S _ hT
  obtain ⟨x₁, hx₁⟩ := hAdm.1.div z
  choose k₁ hk₁ using fun c => hAdm.2 _ c hT (hne z c) z
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (M.O z) S.J (S.TT M z →+ ZMod S.N)
    (fun c => (algebraMap o (M.O z)).mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  let f : (S.TT M z →+ ZMod S.N) → Ω := fun c => S.th x₁ / S.FF _ c (k₁ c)
  have hf : ∀ c, f c ≠ 0 := fun c => div_ne_zero hx₁.1 (hk₁ c).1
  let b : Matrix S.J S.J Ω := Matrix.of fun i j => f (κ i) * algebraMap o Ω (S.proj _ (κ i) j (col i))
  have hb : b.det ≠ 0 := by
    have h1 := (hdet.map (algebraMap (M.O z) Ω)).ne_zero
    rw [RingHom.map_det] at h1
    have h2 := Matrix.det_mul_column (fun i => f (κ i))
      (Matrix.of fun i j => algebraMap o Ω (S.proj _ (κ i) j (col i)))
    change b.det = _ at h2
    rw [h2]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hf _) h1
  suffices h : ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W, _ = Submodule.span (M.O x) (Set.range b) by
    obtain ⟨W, hz, hW⟩ := h
    exact ⟨b, W, hz, hb, hW⟩
  refine exists_opens_span_eq M b _ ?_ ?_ z ?_
  · refine (Set.finite_range fun q : (S.TT M z →+ ZMod S.N) × (S.J × (S.TT M z → ZMod ((S.r * S.N) ^ 2))) ×
      S.Gam × S.J => fun j => S.th q.2.2.1 / S.FF _ q.1 q.2.1 * algebraMap o Ω (S.proj _ q.1 j q.2.2.2)).subset ?_
    rintro _ ⟨c, k, x₀, i, -, -, rfl⟩
    exact ⟨(c, k, x₀, i), rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨κ i, k₁ _, x₁, col i, hk₁ _, hx₁, rfl⟩
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩
    have h1 : ∀ w ∈ Submodule.span (M.O z) {v : S.J → M.O z | ∃ i, κ i = c ∧
        v = fun j => (algebraMap o (M.O z)).mapMatrix (S.proj _ c) j (col i)},
        (fun j => f c * (w j : Ω)) ∈ Submodule.span (M.O z) (Set.range b) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem _ h' =>
        obtain ⟨i', rfl, rfl⟩ := h'
        exact Submodule.subset_span ⟨i', rfl⟩
      | zero =>
        convert Submodule.zero_mem (Submodule.span (M.O z) (Set.range b)) using 1
        funext j
        simp
      | add a a' _ _ ha ha' =>
        convert Submodule.add_mem _ ha ha' using 1
        funext j
        simp [mul_add]
      | smul s a _ ha =>
        convert Submodule.smul_mem _ s ha using 1
        funext j
        simp [Subalgebra.smul_def, mul_left_comm]
    have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
    convert Submodule.smul_mem _ (⟨_, mul_mem (hx₁.2 x₀) (hk.2 (k₁ c))⟩ : M.O z) h2 using 1
    funext j
    have := hx₁.1
    have := (hk₁ c).1
    change _ = S.th x₀ / S.th x₁ * (S.FF _ c (k₁ c) / S.FF _ c k) *
      (S.th x₁ / S.FF _ c (k₁ c) * algebraMap o Ω (S.proj _ c j i))
    field_simp

end GlobalTheory.ZH
