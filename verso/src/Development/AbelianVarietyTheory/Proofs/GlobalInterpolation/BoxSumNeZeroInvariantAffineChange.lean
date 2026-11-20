import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange

open GlobalTheory.Proof.NormalFormAtPrime

/- English proof (translation)
Rewrite using `[← QuotientAddGroup.ker_mk' H, AddSubgroup.relIndex_ker]`. Establish `hf : ((K.map (QuotientAddGroup.mk' H) : AddSubgroup (V ⧸ H)) : Set (V ⧸ H)).Finite`. Use `(S.finite_toSet.image (QuotientAddGroup.mk' H)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Take `⟨s, hs, e⟩` from `h k hk`.

Conclude with `⟨s, hs, (QuotientAddGroup.eq_iff_sub_mem.2 e).symm⟩`. Establish `: Finite (K.map (QuotientAddGroup.mk' H))` using `hf`. Conclude with `Nat.card_pos.ne'`.
-/
theorem relIndex_ne_zero_of_cover {V : Type} [AddCommGroup V] (H K : AddSubgroup V) (S : Finset V)
    (h : ∀ k ∈ K, ∃ s ∈ S, k - s ∈ H) : H.relIndex K ≠ 0 := by
  rw [← QuotientAddGroup.ker_mk' H, AddSubgroup.relIndex_ker]
  have hf : ((K.map (QuotientAddGroup.mk' H) : AddSubgroup (V ⧸ H)) : Set (V ⧸ H)).Finite := by
    refine (S.finite_toSet.image (QuotientAddGroup.mk' H)).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨s, hs, e⟩ := h k hk
    exact ⟨s, hs, (QuotientAddGroup.eq_iff_sub_mem.2 e).symm⟩
  have : Finite (K.map (QuotientAddGroup.mk' H)) := hf
  exact Nat.card_pos.ne'

variable {E : Type} [Field E] [NumberField E]

def lat (P : HeightOneSpectrum (𝓞 E)) (ι : Type) (c : E) : AddSubgroup (ι → E) where
  carrier := {u | ∀ i, IntAt P (c * u i)}
  zero_mem' := fun i => by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  add_mem' := fun {a b} ha hb i => by
    have := (ha i).add (hb i)
    rwa [← mul_add] at this
  neg_mem' := fun {a} ha i => by
    have := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (ha i)
    simpa using this

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lat {P : HeightOneSpectrum (𝓞 E)} {ι : Type} {c : E} {u : ι → E} :
    u ∈ lat P ι c ↔ ∀ i, IntAt P (c * u i) := Iff.rfl

/- English proof (translation)
Introduce `u hu i` and use `by rw [h, mul_assoc] exact intAt_pow_mul k (hu i)`.
-/
theorem lat_le {P : HeightOneSpectrum (𝓞 E)} {ι : Type} {c c' : E} (k : ℕ) (h : c' = (qOf P : E) ^ k * c) :
    lat P ι c ≤ lat P ι c' := fun u hu i => by
  rw [h, mul_assoc]
  exact intAt_pow_mul k (hu i)

/- English proof (translation)
Use `choose m hm using h`. Use `⟨Finset.univ.sup fun k => m (x k), fun m' hm' k => intAt_pow_mono (le_trans ?_ hm') (hm (x k))⟩` and prove the remaining obligations. Conclude with `Finset.le_sup (f := fun k => m (x k)) (Finset.mem_univ k)`.
-/
theorem exists_fin {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {κ : Type} [Fintype κ] (x : κ → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ k, IntAt P ((qOf P : E) ^ m' * x k) := by
  choose m hm using h
  refine ⟨Finset.univ.sup fun k => m (x k), fun m' hm' k => intAt_pow_mono (le_trans ?_ hm') (hm (x k))⟩
  exact Finset.le_sup (f := fun k => m (x k)) (Finset.mem_univ k)

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_fin h (fun p : ι × ι => T (Pi.single p.1 1) p.2)`. Use `⟨m, fun m' hm' c u hu l => ?_⟩` and prove the remaining obligations. Establish `e : T u = ∑ s, u s • T (Pi.single s 1)` using `by conv_lhs => rw [show u = ∑ s, u s • (Pi.single s (1 : E) : ι → E) from by`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]]`.

Simplify using `only [map_sum, map_smul]`. Rewrite using `[e, Finset.sum_apply, Finset.mul_sum]`. Use `intAt_sum _ _ fun s _ => ?_` and prove the remaining obligations. Use `(hu s).mul (hm m' hm' (s, l))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_bound {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {ι : Type} [Fintype ι] [DecidableEq ι] (T : (ι → E) →ₗ[E] (ι → E)) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ (c : E) (u : ι → E), u ∈ lat P ι c → T u ∈ lat P ι ((qOf P : E) ^ m' * c) := by
  obtain ⟨m, hm⟩ := exists_fin h (fun p : ι × ι => T (Pi.single p.1 1) p.2)
  refine ⟨m, fun m' hm' c u hu l => ?_⟩
  have e : T u = ∑ s, u s • T (Pi.single s 1) := by
    conv_lhs => rw [show u = ∑ s, u s • (Pi.single s (1 : E) : ι → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply, Finset.mul_sum]
  refine intAt_sum _ _ fun s _ => ?_
  have := (hu s).mul (hm m' hm' (s, l))
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `h1 h2 h3 E _ _ K _ _ P hP ι _ _ f N hf T b`. Establish `hq` using `qOf_ne_zero P`. Establish `hs : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x)` using `fun x => by`. Take `⟨m, hm⟩` from `(h1 E P 1 1).1 (fun _ => x)`. Conclude with `⟨m, hm m le_rfl 0⟩`.

Establish `sep : ∀ A B : ℕ, ∀ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), ∀ s' ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), s - s' ∈ lat P ι ((qOf P : E) ^ B)⁻¹ → s = s'` using `fun A B s hs s' hs' h => by`. Use function extensionality and compare the values at `i`. Conclude with `(h3 E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)`. Establish `cov : ∀ A B : ℕ, ∀ v ∈ lat P ι ((qOf P : E) ^ A), ∃ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), v - s ∈ lat P ι ((qOf P : E) ^ B)⁻¹` using `fun A B v hv => by choose s hs hs' using fun i => (h3 E P hP A B).2 (v i) (hv i)`. Conclude with `⟨s, Fintype.mem_piFinset.2 hs, hs'⟩`.

Establish `inv : ∀ v, ∀ u ∈ lat P ι ((qOf P : E) ^ N)⁻¹, f (v + u) = f v` using `fun v u hu => by`. Use `hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul]`. Then use the resulting hypothesis. Take `⟨m1, hm1⟩` from `exists_bound hs T.toLinearMap`. Take `⟨m2, hm2⟩` from `exists_bound hs T.symm.toLinearMap`.

Take `⟨m3, hm3⟩` from `exists_fin hs b`. Take `⟨m, a1, a2, a3⟩ : ∃ m, m1 ≤ m ∧ m2 ≤ m ∧ m3 ≤ m` from `⟨m1 + m2 + m3, by omega, by omega, by omega⟩`. Establish `hT` using `hm1 m a1`. Establish `hT'` using `hm2 m a2`. Establish `hb : b ∈ lat P ι ((qOf P : E) ^ m)` using `hm3 m a3`.

Simplify using `only [LinearEquiv.coe_coe] at hT hT'`. Use `⟨N + 2 * m, N + 2 * m, fun A B hA hB => ?_⟩` and prove the remaining obligations. Take `⟨A, rfl⟩` from `Nat.exists_eq_add_of_le hA`. Take `⟨B, rfl⟩` from `Nat.exists_eq_add_of_le hB`. Use `set A' := N + 2 * m + A with hA'`.

Use `set B' := N + 2 * m + B with hB'`. Set `L : AddSubgroup (ι → E)` to `lat P ι ((qOf P : E) ^ B')⁻¹`. Set `L' : AddSubgroup (ι → E)` to `L.comap T.symm.toLinearMap.toAddMonoidHom`. Establish `mL' : ∀ u, u ∈ L' ↔ T.symm u ∈ L` using `fun u => Iff.rfl`. Establish `hL'le : L' ≤ lat P ι ((qOf P : E) ^ m * ((qOf P : E) ^ B')⁻¹)` using `fun u hu => by`.

Use `hT _ _ ((mL' u).1 hu)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hleL' : lat P ι ((qOf P : E) ^ (B' + m))⁻¹ ≤ L'` using `fun u hu => by`. Use `hT' _ _ hu` as an intermediate fact. Rewrite using `[mL']`.

Use `this using 2` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hLN : L ≤ lat P ι ((qOf P : E) ^ N)⁻¹` using `lat_le (2 * m + B) (by rw [hB']; field_simp; ring)`. Establish `hL'N : L' ≤ lat P ι ((qOf P : E) ^ N)⁻¹` using `hL'le.trans (lat_le (m + B) (by rw [hB']; field_simp; ring))`.

Establish `hN0 : lat P ι ((qOf P : E) ^ N)⁻¹ ≤ lat P ι ((qOf P : E) ^ 0)` using `lat_le N (by field_simp)`. Establish `hinj : Function.Injective fun t => T t + b` using `fun s t h => T.injective (add_right_cancel h)`. Establish `key` using `h2 (ι → E) K f L L' (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B') ((Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B').image fun t => T t + b) (relIndex_ne_zero_of_cover _ _ _ fun k hk => by`. Take `⟨s, hs, e⟩` from `cov 0 (B' + m) k (hN0 (hLN hk))`. Conclude with `⟨s, hs, hleL' e⟩)`.

Use the proof step `(relIndex_ne_zero_of_cover _ _ _ fun k hk => cov 0 B' k (hN0 (hL'N hk)))`. Use the proof step `(fun v u hu => inv v u (hLN hu)) (fun v u hu => inv v u (hL'N hu)) (sep A' B')`. Use the proof step `(fun v hv => cov A' B' v (lat_le (c := (qOf P : E) ^ N) (2 * m + A) (by rw [hA']; ring) (hf.1 v hv)))`. Use the proof step `(fun s hs s' hs' h => by`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hs`.

Take `⟨t', ht', rfl⟩` from `Finset.mem_image.1 hs'`. Rewrite `h` using `[mL', add_sub_add_right_eq_sub, ← map_sub, LinearEquiv.symm_apply_apply]`. Rewrite using `[sep A' B' t ht t' ht' h])`. Use the proof step `(fun v hv => by`. Establish `e1 : v - b ∈ lat P ι ((qOf P : E) ^ (N + m))` using `sub_mem (lat_le (c := (qOf P : E) ^ N) m (by ring) (hf.1 v hv)) (lat_le N (by ring) hb)`.

Take `⟨s, hs, e⟩` from `cov A' B' _ (lat_le A (by rw [hA']; ring) (hT' _ _ e1))`. Use `⟨T s + b, Finset.mem_image_of_mem _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mL']`. Use `e using 1` and compare the differences between its conclusion and the goal. Rewrite using `[show v - (T s + b) = (v - b) - T s by abel, map_sub, LinearEquiv.symm_apply_apply])`.

Rewrite `key` using `[Finset.sum_image hinj.injOn]`. Establish `hqK : (qOf P : K) ≠ 0`. Establish `: qOf P ≠ 0` using `fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `this` after adjusting the coercions. Establish `hw : (((qOf P : K) ^ B')⁻¹) ^ Fintype.card ι ≠ 0` using `pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hqK))`.

Unfold `boxSum`. Rewrite using `[mul_ne_zero_iff_left hw, mul_ne_zero_iff_left hw]`. Conclude with `key.symm`.
-/
theorem affine : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  classical
  intro h1 h2 h3 E _ _ K _ _ P hP ι _ _ f N hf T b
  have hq := qOf_ne_zero P
  have hs : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x) := fun x => by
    obtain ⟨m, hm⟩ := (h1 E P 1 1).1 (fun _ => x)
    exact ⟨m, hm m le_rfl 0⟩
  have sep : ∀ A B : ℕ, ∀ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      ∀ s' ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      s - s' ∈ lat P ι ((qOf P : E) ^ B)⁻¹ → s = s' := fun A B s hs s' hs' h => by
    funext i
    exact (h3 E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  have cov : ∀ A B : ℕ, ∀ v ∈ lat P ι ((qOf P : E) ^ A),
      ∃ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), v - s ∈ lat P ι ((qOf P : E) ^ B)⁻¹ :=
    fun A B v hv => by
      choose s hs hs' using fun i => (h3 E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩
  have inv : ∀ v, ∀ u ∈ lat P ι ((qOf P : E) ^ N)⁻¹, f (v + u) = f v := fun v u hu => by
    have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  obtain ⟨m1, hm1⟩ := exists_bound hs T.toLinearMap
  obtain ⟨m2, hm2⟩ := exists_bound hs T.symm.toLinearMap
  obtain ⟨m3, hm3⟩ := exists_fin hs b
  obtain ⟨m, a1, a2, a3⟩ : ∃ m, m1 ≤ m ∧ m2 ≤ m ∧ m3 ≤ m := ⟨m1 + m2 + m3, by omega, by omega, by omega⟩
  have hT := hm1 m a1
  have hT' := hm2 m a2
  have hb : b ∈ lat P ι ((qOf P : E) ^ m) := hm3 m a3
  simp only [LinearEquiv.coe_coe] at hT hT'
  refine ⟨N + 2 * m, N + 2 * m, fun A B hA hB => ?_⟩
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le hB
  set A' := N + 2 * m + A with hA'
  set B' := N + 2 * m + B with hB'
  let L : AddSubgroup (ι → E) := lat P ι ((qOf P : E) ^ B')⁻¹
  let L' : AddSubgroup (ι → E) := L.comap T.symm.toLinearMap.toAddMonoidHom
  have mL' : ∀ u, u ∈ L' ↔ T.symm u ∈ L := fun u => Iff.rfl
  have hL'le : L' ≤ lat P ι ((qOf P : E) ^ m * ((qOf P : E) ^ B')⁻¹) := fun u hu => by
    have := hT _ _ ((mL' u).1 hu)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hleL' : lat P ι ((qOf P : E) ^ (B' + m))⁻¹ ≤ L' := fun u hu => by
    have := hT' _ _ hu
    rw [mL']
    convert this using 2
    field_simp
    ring
  have hLN : L ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := lat_le (2 * m + B) (by rw [hB']; field_simp; ring)
  have hL'N : L' ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := hL'le.trans (lat_le (m + B) (by rw [hB']; field_simp; ring))
  have hN0 : lat P ι ((qOf P : E) ^ N)⁻¹ ≤ lat P ι ((qOf P : E) ^ 0) := lat_le N (by field_simp)
  have hinj : Function.Injective fun t => T t + b := fun s t h => T.injective (add_right_cancel h)
  have key := h2 (ι → E) K f L L' (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B')
    ((Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B').image fun t => T t + b)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => by
      obtain ⟨s, hs, e⟩ := cov 0 (B' + m) k (hN0 (hLN hk))
      exact ⟨s, hs, hleL' e⟩)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => cov 0 B' k (hN0 (hL'N hk)))
    (fun v u hu => inv v u (hLN hu)) (fun v u hu => inv v u (hL'N hu)) (sep A' B')
    (fun v hv => cov A' B' v (lat_le (c := (qOf P : E) ^ N) (2 * m + A) (by rw [hA']; ring) (hf.1 v hv)))
    (fun s hs s' hs' h => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
      rw [mL', add_sub_add_right_eq_sub, ← map_sub, LinearEquiv.symm_apply_apply] at h
      rw [sep A' B' t ht t' ht' h])
    (fun v hv => by
      have e1 : v - b ∈ lat P ι ((qOf P : E) ^ (N + m)) :=
        sub_mem (lat_le (c := (qOf P : E) ^ N) m (by ring) (hf.1 v hv)) (lat_le N (by ring) hb)
      obtain ⟨s, hs, e⟩ := cov A' B' _ (lat_le A (by rw [hA']; ring) (hT' _ _ e1))
      refine ⟨T s + b, Finset.mem_image_of_mem _ hs, ?_⟩
      rw [mL']
      convert e using 1
      rw [show v - (T s + b) = (v - b) - T s by abel, map_sub, LinearEquiv.symm_apply_apply])
  rw [Finset.sum_image hinj.injOn] at key
  have hqK : (qOf P : K) ≠ 0 := by
    have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hw : (((qOf P : K) ^ B')⁻¹) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hqK))
  unfold boxSum
  rw [mul_ne_zero_iff_left hw, mul_ne_zero_iff_left hw]
  exact key.symm

end GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange
