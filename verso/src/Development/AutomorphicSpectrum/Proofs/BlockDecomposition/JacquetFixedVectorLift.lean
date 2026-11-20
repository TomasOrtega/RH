import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralStrictlyDominantExistsStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFixedLift
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VecStab

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

noncomputable section

namespace GlobalTheory.CompanionTheory.JacquetLemma

noncomputable def vecStab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (u : V) :
    Subgroup G :=
  _root_.UpperTheory.Reformulated.B.VectorStabilizer₂.vecStab π u

def cosetStab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (q : Submodule ℂ V) (u : V) : Subgroup G where
  carrier := {x | ∀ v, π x v - u ∈ q ↔ v - u ∈ q}
  mul_mem' := by
    intro a b ha hb v
    rw [map_mul, Module.End.mul_apply, ha, hb]
  one_mem' := by intro v; simp
  inv_mem' := by
    intro a ha v
    have := ha (π a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

/- English proof (translation)
Establish `step : ∀ x, A x ∈ S → x ∈ S`. Introduce `x hx`. Set `B : S →ₗ[ℂ] S` to `LinearMap.restrict A hS`. Establish `hB : Function.Injective B`. Introduce `p q h`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `hA` to reduce the goal to its premises. Conclude with `congrArg Subtype.val h`. Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.1 hB) ⟨A x, hx⟩`. Establish `h2 : A y = A x` using `congrArg Subtype.val hy`.

Rewrite using `[← hA h2]`. Conclude with `y.2`. Proceed by induction on `j with`. Consider the case `zero => simpa using hw`. Consider the case `succ n ih`.

Apply `ih` to reduce the goal to its premises. Apply `step` to reduce the goal to its premises. Rewrite using `[← Module.End.mul_apply, ← pow_succ']`. Conclude with `hw`.
-/
theorem mem_of_pow_mem {Q : Type} [AddCommGroup Q] [Module ℂ Q] (S : Submodule ℂ Q)
    [FiniteDimensional ℂ S] (A : Module.End ℂ Q) (hA : Function.Injective A)
    (hS : ∀ x ∈ S, A x ∈ S) (j : ℕ) (w : Q) (hw : (A ^ j) w ∈ S) : w ∈ S := by
  have step : ∀ x, A x ∈ S → x ∈ S := by
    intro x hx
    let B : S →ₗ[ℂ] S := LinearMap.restrict A hS
    have hB : Function.Injective B := by
      intro p q h
      apply Subtype.ext
      apply hA
      exact congrArg Subtype.val h
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hB) ⟨A x, hx⟩
    have h2 : A y = A x := congrArg Subtype.val hy
    rw [← hA h2]
    exact y.2
  induction j with
  | zero => simpa using hw
  | succ n ih =>
    apply ih
    apply step
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hw

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift J L A hJo hJc π hπ q u hLJ hLu hAJ hAq hfact`.
-/
theorem exists_fixed_lift {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (J L A : Subgroup G) (hJo : IsOpen (J : Set G))
    (hJc : IsCompact (J : Set G)) (π : Representation ℂ G V) (hπ : IsSmooth π)
    (q : Submodule ℂ V) (u : V) (hLJ : L ≤ J) (hLu : ∀ y ∈ L, π y u = u) (hAJ : A ≤ J)
    (hAq : ∀ x ∈ A, π x u - u ∈ q) (hfact : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) :
    ∃ v ∈ fixed π J, v - u ∈ q :=
  _root_.UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift J L A hJo hJc π hπ q u hLJ hLu hAJ hAq hfact

/- English proof (translation)
Introduce `x y h`. Use `congrArg (ρ g⁻¹) h` as an intermediate fact. Simplify `this` using `[← Module.End.mul_apply, ← map_mul]`.
-/
theorem rep_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) : Function.Injective (ρ g) := by
  intro x y h
  have := congrArg (ρ g⁻¹) h
  simpa [← Module.End.mul_apply, ← map_mul] using this

end GlobalTheory.CompanionTheory.JacquetLemma

namespace GlobalTheory.CompanionTheory.JacquetLemma

/- English proof (translation)
Introduce `k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ w hw`. Take `⟨a, hac, hstrict, hshrink⟩` from `GlobalTheory.T.central_strictly_dominant_exists k N h d hd J hJo hJc hI hpos`. Take `⟨T, hT⟩` from `GlobalTheory.T.jacquet_hecke_condition_holds k N J hJo hJc V π hπ.1 (leviEmb k (stdBlocks d hd) a)`. Establish `hC2` using `GlobalTheory.T.jacquet_hecke_compat_holds k N h d hd J hJo hJc hI hpos V π hπ.1 a hstrict.1 T hT`. Use `haveI : FiniteDimensional ℂ (fixed π J) := hπ.2 J hJo hJc`.

Use `set q := twKer π (unipRad k (stdBlocks d hd)) 1 with hq`. Set `p : fixed π J →ₗ[ℂ] (V ⧸ q)` to `q.mkQ.comp (fixed π J).subtype`. Set `S : Submodule ℂ (V ⧸ q)` to `LinearMap.range p`. Use `haveI : FiniteDimensional ℂ S := inferInstanceAs (FiniteDimensional ℂ (LinearMap.range p))`. Set `A : Module.End ℂ (V ⧸ q)` to `jac (stdBlocks d hd) π a`.

Establish `hAinj : Function.Injective A` using `rep_injective _ a`. Establish `hAS : ∀ x ∈ S, A x ∈ S`. Introduce and unpack `_ ⟨v, rfl⟩`. Use `⟨(((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v, ?_⟩` and prove the remaining obligations. Establish `h1` using `hC2 v`.

Use `show (Submodule.Quotient.mk (((((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v : fixed π J) : V) : V ⧸ q) = A (Submodule.Quotient.mk (v : V))`. Rewrite using `[Submodule.coe_smul, Submodule.Quotient.mk_smul, h1, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨j, hj⟩` from `hshrink {x | π x u = u} (hπ.1 u) (by simp)`. Use `set g := leviEmb k (stdBlocks d hd) a with hg`.

Use `set u' : V := π (g ^ j) u with hu'`. Establish `hpow : (A ^ j) (Submodule.Quotient.mk u) = (((deltaHalf k (Bl d) (a ^ j))⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk u' : V ⧸ q)`. Establish `h1 : A ^ j = jac (stdBlocks d hd) π (a ^ j)` using `(map_pow (jac (stdBlocks d hd) π) a j).symm`. Establish `h2 : leviEmb k (stdBlocks d hd) (a ^ j) = g ^ j` using `map_pow _ _ _`. Rewrite using `[h1, jac_mk, h2]`.

Establish `hLu : ∀ y ∈ KNl k N J d hd, π y u' = u'`. Introduce `y hy`. Establish `h2 : π ((g ^ j)⁻¹ * y * g ^ j) u = u` using `hj y hy`. Establish `h3 : y * g ^ j = g ^ j * ((g ^ j)⁻¹ * y * g ^ j)` using `by group`. Rewrite using `[hu', ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply, h2]`.

Establish `hM : ∀ m ∈ KM k N J d hd, π (leviEmb k (stdBlocks d hd) m) u' - u' ∈ q`. Introduce `m hm`. Establish `h1 : jac (stdBlocks d hd) π m (Submodule.Quotient.mk u) = Submodule.Quotient.mk u`. Use `hw ⟨m, hm⟩` as an intermediate fact. Simplify using `using this`.

Rewrite `h1` using `[jac_mk, GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hJc m hm]`. Simplify using `only [inv_one, Units.val_one, one_smul] at h1`. Establish `h2 : (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u) : V ⧸ q) = Submodule.Quotient.mk u` using `h1`. Establish `h3 : jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u)) = jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk u)` using `congrArg _ h2`. Establish `h4 : (Submodule.Quotient.mk (π (g ^ j) (π (leviEmb k (stdBlocks d hd) m) u)) : V ⧸ q) = Submodule.Quotient.mk u'`.

Establish `e1 : ∀ z : V, jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (g ^ j) z) : V ⧸ q)`. Introduce `z`. Rewrite using `[hg, ← map_pow]`. Both sides reduce to the same expression. Rewrite `h3` using `[e1, e1]`.

Conclude with `h3`. Establish `hcomm : leviEmb k (stdBlocks d hd) m * g ^ j = g ^ j * leviEmb k (stdBlocks d hd) m`. Establish `: m * a ^ j = a ^ j * m` using `((Commute.pow_right (show Commute m a from (hac m).symm) j))`. Use `congrArg (leviEmb k (stdBlocks d hd)) this` as an intermediate fact. Simplify `this` using `[map_mul, map_pow, hg]`.

Rewrite using `[← Submodule.Quotient.eq, hu', ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]`. Conclude with `h4`. Establish `hMstab : ∀ m ∈ KM k N J d hd, leviEmb k (stdBlocks d hd) m ∈ cosetStab π q u'`. Introduce `m hm v`. Establish `h1` using `hM m hm`.

Establish `hinj` using `rep_injective (jacU (stdBlocks d hd) π) m`. Establish `e1 : ∀ z : V, jacU (stdBlocks d hd) π m (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) z) : V ⧸ q)` using `fun z => rfl`. Rewrite `h1`, the goal using `[← Submodule.Quotient.eq]`. Rewrite using `[← Submodule.Quotient.eq, ← e1]`. Use `conv_lhs => rw [← h1, ← e1]`.

Conclude with `hinj.eq_iff`. Establish `hNstab : ∀ c ∈ unipRad k (stdBlocks d hd), c ∈ cosetStab π q u'`. Introduce `c hc v`. Establish `h1 : π c v - v ∈ q`. Use `Submodule.subset_span ⟨⟨c, hc⟩, v, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[← Submodule.Quotient.eq, ← Submodule.Quotient.eq, (Submodule.Quotient.eq q).2 h1]`. Take `⟨v, hv, hvu⟩` from `exists_fixed_lift J (KNl k N J d hd) (J ⊓ cosetStab π q u') hJo hJc π hπ.1 q u' inf_le_left hLu inf_le_left (fun x hx => by`. Use `(hx.2 u').2 (by simp)` as an intermediate fact. Conclude with `this)`.

Use the proof step `(fun y hy => by`. Take `⟨a', ha', b, hb, c, hc, hy'⟩` from `hI y⁻¹ (inv_mem hy)`. Take `⟨m, hm⟩` from `hb.2`. Establish `hmK : m ∈ KM k N J d hd` using `by show leviEmb k (stdBlocks d hd) m ∈ J`. Rewrite using `[hm]`.

Conclude with `hb.1`. Establish `hbS : b ∈ cosetStab π q u'` using `hm ▸ hMstab m hmK`. Use `⟨c⁻¹ * b⁻¹, ⟨J.mul_mem (J.inv_mem hc.1) (J.inv_mem hb.1), (cosetStab π q u').mul_mem ((cosetStab π q u').inv_mem (hNstab c hc.2)) ((cosetStab π q u').inv_mem hbS)⟩, ?_⟩` and prove the remaining obligations. Establish `h5 : (c⁻¹ * b⁻¹)⁻¹ * y = a'⁻¹`. Establish `: y = (a' * b * c)⁻¹` using `by rw [← hy']; simp`.

Rewrite using `[this]`. Use `group`. Rewrite using `[h5]`. Conclude with `inv_mem ha')`. Establish `hS' : (Submodule.Quotient.mk u' : V ⧸ q) ∈ S` using `⟨⟨v, hv⟩, (Submodule.Quotient.eq q).2 hvu⟩`.

Establish `hmem : (Submodule.Quotient.mk u : V ⧸ q) ∈ S`. Use `mem_of_pow_mem S A hAinj hAS j _ ?_` and prove the remaining obligations. Rewrite using `[hpow]`. Conclude with `S.smul_mem _ hS'`. Take `⟨v', hv'⟩` from `hmem`.

Conclude with `⟨v', hv'⟩`.
-/
theorem jacquet_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ w hw
  obtain ⟨a, hac, hstrict, hshrink⟩ := GlobalTheory.T.central_strictly_dominant_exists k N h d hd J hJo hJc hI hpos
  obtain ⟨T, hT⟩ := GlobalTheory.T.jacquet_hecke_condition_holds k N J hJo hJc V π hπ.1 (leviEmb k (stdBlocks d hd) a)
  have hC2 := GlobalTheory.T.jacquet_hecke_compat_holds k N h d hd J hJo hJc hI hpos V π hπ.1 a hstrict.1 T hT
  haveI : FiniteDimensional ℂ (fixed π J) := hπ.2 J hJo hJc
  set q := twKer π (unipRad k (stdBlocks d hd)) 1 with hq
  let p : fixed π J →ₗ[ℂ] (V ⧸ q) := q.mkQ.comp (fixed π J).subtype
  let S : Submodule ℂ (V ⧸ q) := LinearMap.range p
  haveI : FiniteDimensional ℂ S := inferInstanceAs (FiniteDimensional ℂ (LinearMap.range p))
  let A : Module.End ℂ (V ⧸ q) := jac (stdBlocks d hd) π a
  have hAinj : Function.Injective A := rep_injective _ a
  have hAS : ∀ x ∈ S, A x ∈ S := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v, ?_⟩
    have h1 := hC2 v
    show (Submodule.Quotient.mk (((((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v : fixed π J) : V) : V ⧸ q) = A (Submodule.Quotient.mk (v : V))
    rw [Submodule.coe_smul, Submodule.Quotient.mk_smul, h1, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨j, hj⟩ := hshrink {x | π x u = u} (hπ.1 u) (by simp)
  set g := leviEmb k (stdBlocks d hd) a with hg
  set u' : V := π (g ^ j) u with hu'

  have hpow : (A ^ j) (Submodule.Quotient.mk u) =
      (((deltaHalf k (Bl d) (a ^ j))⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk u' : V ⧸ q) := by
    have h1 : A ^ j = jac (stdBlocks d hd) π (a ^ j) := (map_pow (jac (stdBlocks d hd) π) a j).symm
    have h2 : leviEmb k (stdBlocks d hd) (a ^ j) = g ^ j := map_pow _ _ _
    rw [h1, jac_mk, h2]

  have hLu : ∀ y ∈ KNl k N J d hd, π y u' = u' := by
    intro y hy
    have h2 : π ((g ^ j)⁻¹ * y * g ^ j) u = u := hj y hy
    have h3 : y * g ^ j = g ^ j * ((g ^ j)⁻¹ * y * g ^ j) := by group
    rw [hu', ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply, h2]

  have hM : ∀ m ∈ KM k N J d hd, π (leviEmb k (stdBlocks d hd) m) u' - u' ∈ q := by
    intro m hm
    have h1 : jac (stdBlocks d hd) π m (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := by
      have := hw ⟨m, hm⟩
      simpa using this
    rw [jac_mk, GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hJc m hm] at h1
    simp only [inv_one, Units.val_one, one_smul] at h1
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u) : V ⧸ q) = Submodule.Quotient.mk u := h1
    have h3 : jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u)) =
        jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk u) := congrArg _ h2
    have h4 : (Submodule.Quotient.mk (π (g ^ j) (π (leviEmb k (stdBlocks d hd) m) u)) : V ⧸ q) = Submodule.Quotient.mk u' := by
      have e1 : ∀ z : V, jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (g ^ j) z) : V ⧸ q) := by
        intro z
        rw [hg, ← map_pow]
        rfl
      rw [e1, e1] at h3
      exact h3
    have hcomm : leviEmb k (stdBlocks d hd) m * g ^ j = g ^ j * leviEmb k (stdBlocks d hd) m := by
      have : m * a ^ j = a ^ j * m := ((Commute.pow_right (show Commute m a from (hac m).symm) j))
      have := congrArg (leviEmb k (stdBlocks d hd)) this
      simpa [map_mul, map_pow, hg] using this
    rw [← Submodule.Quotient.eq, hu', ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    exact h4
  have hMstab : ∀ m ∈ KM k N J d hd, leviEmb k (stdBlocks d hd) m ∈ cosetStab π q u' := by
    intro m hm v
    have h1 := hM m hm
    have hinj := rep_injective (jacU (stdBlocks d hd) π) m
    have e1 : ∀ z : V, jacU (stdBlocks d hd) π m (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) z) : V ⧸ q) := fun z => rfl
    rw [← Submodule.Quotient.eq] at h1 ⊢
    rw [← Submodule.Quotient.eq, ← e1]
    conv_lhs => rw [← h1, ← e1]
    exact hinj.eq_iff
  have hNstab : ∀ c ∈ unipRad k (stdBlocks d hd), c ∈ cosetStab π q u' := by
    intro c hc v
    have h1 : π c v - v ∈ q := by
      refine Submodule.subset_span ⟨⟨c, hc⟩, v, ?_⟩
      simp
    rw [← Submodule.Quotient.eq, ← Submodule.Quotient.eq, (Submodule.Quotient.eq q).2 h1]
  obtain ⟨v, hv, hvu⟩ := exists_fixed_lift J (KNl k N J d hd) (J ⊓ cosetStab π q u') hJo hJc π hπ.1 q u'
    inf_le_left hLu inf_le_left
    (fun x hx => by
      have := (hx.2 u').2 (by simp)
      exact this)
    (fun y hy => by
      obtain ⟨a', ha', b, hb, c, hc, hy'⟩ := hI y⁻¹ (inv_mem hy)
      obtain ⟨m, hm⟩ := hb.2
      have hmK : m ∈ KM k N J d hd := by
        show leviEmb k (stdBlocks d hd) m ∈ J
        rw [hm]; exact hb.1
      have hbS : b ∈ cosetStab π q u' := hm ▸ hMstab m hmK
      refine ⟨c⁻¹ * b⁻¹, ⟨J.mul_mem (J.inv_mem hc.1) (J.inv_mem hb.1),
        (cosetStab π q u').mul_mem ((cosetStab π q u').inv_mem (hNstab c hc.2)) ((cosetStab π q u').inv_mem hbS)⟩, ?_⟩
      have h5 : (c⁻¹ * b⁻¹)⁻¹ * y = a'⁻¹ := by
        have : y = (a' * b * c)⁻¹ := by rw [← hy']; simp
        rw [this]; group
      rw [h5]
      exact inv_mem ha')
  have hS' : (Submodule.Quotient.mk u' : V ⧸ q) ∈ S :=
    ⟨⟨v, hv⟩, (Submodule.Quotient.eq q).2 hvu⟩
  have hmem : (Submodule.Quotient.mk u : V ⧸ q) ∈ S := by
    refine mem_of_pow_mem S A hAinj hAS j _ ?_
    rw [hpow]
    exact S.smul_mem _ hS'
  obtain ⟨v', hv'⟩ := hmem
  exact ⟨v', hv'⟩

end GlobalTheory.CompanionTheory.JacquetLemma
