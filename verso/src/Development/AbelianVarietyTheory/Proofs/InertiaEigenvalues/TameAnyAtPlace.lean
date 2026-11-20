import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatioStatement

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Unfold `Formalism.CyclotomicNorms.primeToPart`. Break down `Nat.eq_zero_or_pos (orderOf x) with h0 | hpos` into its components or cases. Rewrite using `[h0]`. Establish `e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1`.

Introduce `n hn`. Substitute `hn` using the available equality. Rewrite using `[Nat.cast_one, ZMod.inv_one]`. Both sides reduce to the same expression. Establish `e0 : l ^ (Nat.factorization 0) l = 1` using `by simp`.

Rewrite using `[e0, e _ (by simp)]`. Simplify using the standard rewrite rules. Use `set a := (orderOf x).factorization l with ha set m := orderOf x / l ^ a with hm`. Establish `hmul : l ^ a * m = orderOf x` using `Nat.ordProj_mul_ordCompl_eq_self _ _`. Establish `hcop : Nat.Coprime (l ^ a) m` using `(Nat.coprime_ordCompl hl hpos.ne').pow_left _`.

Establish `hmpos : 0 < m` using `Nat.ordCompl_pos l hpos.ne'`. Use `haveI : NeZero m := ⟨hmpos.ne'⟩`. Establish `h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a`. Rewrite using `[← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]`. Establish `h2 : ι x ^ m = 1`.

Use `iterateFrobenius_inj K l a` as an intermediate fact. Conclude with `this (by simpa [iterateFrobenius_def] using h1)`. Establish `h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Move the coercions through the operations in `[ZMod.natCast_zmod_val]`.

Use `ZMod.coe_mul_inv_eq_one (l ^ a) hcop` as an intermediate fact. Simplify using `using this`. Rewrite using `[map_pow]`. Establish `h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1`. Rewrite using `[pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]`.

Rewrite using `[h4, pow_one]`.
-/
theorem tameAnyFix_map_primeToPart {M K : Type} [Monoid M] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l]
    (ι : M →* K) (x : M) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  have hl : l.Prime := Fact.out
  unfold Formalism.CyclotomicNorms.primeToPart
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0]
    have e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
      intro n hn
      subst hn
      rw [Nat.cast_one, ZMod.inv_one]
      rfl
    have e0 : l ^ (Nat.factorization 0) l = 1 := by simp
    rw [e0, e _ (by simp)]
    simp
  · set a := (orderOf x).factorization l with ha
    set m := orderOf x / l ^ a with hm
    have hmul : l ^ a * m = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : Nat.Coprime (l ^ a) m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
    have hmpos : 0 < m := Nat.ordCompl_pos l hpos.ne'
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a := by
      rw [← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 : ι x ^ m = 1 := by
      have := iterateFrobenius_inj K l a
      exact this (by simpa [iterateFrobenius_def] using h1)
    have h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast [ZMod.natCast_zmod_val]
      have := ZMod.coe_mul_inv_eq_one (l ^ a) hcop
      simpa using this
    rw [map_pow]
    have h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1 := by
      rw [pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]
    rw [h4, pow_one]

/- English proof (translation)
Simplify using `[isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]`.
-/
theorem tameAnyFix_isoLoc (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

/- English proof (translation)
Introduce `hl`. Establish `hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal` using `D.naut.plGw_over k v`. Establish `hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal` using `hl`. Establish `hc : Nat.Coprime (D.nd.l i) (D.host.g k)` using `(Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h`. Establish `hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E)` using `Nat.Coprime.cast hc`.

Take `⟨a, b, hab⟩` from `hc'`. Apply `(D.naut.plGw k v).isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)`.
-/
theorem tameAnyFix_not_over (D : D7) (i : D.nd.Loc) (k : Fin 2) (h : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
  intro hl
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := hl
  have hc : Nat.Coprime (D.nd.l i) (D.host.g k) := (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h
  have hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hc
  obtain ⟨a, b, hab⟩ := hc'
  apply (D.naut.plGw k v).isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)

/- English proof (translation)
Introduce `D hA hF i π ρ hc hr hfull hρ k hk v`. Use `haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩`. Take `⟨ι, hinj, hred⟩` from `GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hk`. Establish `hpol` using `GlobalTheory.T.inertia_charpoly_eq D hA hF i π ρ hc hr hρ _ (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)`. Establish `hlab` using `D.ntypes.inertiaCharpoly_type k v _ (hfull k v)`.

Rewrite `hpol` using `[← tameAnyFix_isoLoc D π, hlab]`. Establish `h1` using `hred _ _ hpol`. Establish `hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) = ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map fun x => X - C (ι (Formalism.Cyclotomi …`. Rewrite using `[D.ntypes.heckeLoc_gamma_places]`. Simplify using `only [zpow_one, tameAnyFix_map_primeToPart]`.

Rewrite using `[← h1, ← Matrix.charpoly_map]`. Both sides reduce to the same expression. Establish `hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k), iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y → D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y`. Introduce `y hy`. Establish `h2` using `hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])`.

Rewrite using `[D.ntypes.heckeLoc_gamma_places]`. Simplify using `using h2`. Break down `D.ntypes.chiT_tg i k v hk with h | h` into its components or cases. Use `⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_one, tameAnyFix_map_primeToPart]`.

Conclude with `hval _ h`. Use `⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]`.
-/
theorem tameAnyAt_fixed : ∀ D : D7, GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  intro D hA hF i π ρ hc hr hfull hρ k hk v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨ι, hinj, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hk
  have hpol := GlobalTheory.T.inertia_charpoly_eq D hA hF i π ρ hc hr hρ _ (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)
  have hlab := D.ntypes.inertiaCharpoly_type k v _ (hfull k v)
  rw [← tameAnyFix_isoLoc D π, hlab] at hpol
  have h1 := hred _ _ hpol
  have hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ (1 : ℤ))).prod := by
    rw [D.ntypes.heckeLoc_gamma_places]
    simp only [zpow_one, tameAnyFix_map_primeToPart]
    rw [← h1, ← Matrix.charpoly_map]
    rfl
  have hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k),
      iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y →
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y := by
    intro y hy
    have h2 := hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])
    rw [D.ntypes.heckeLoc_gamma_places]
    simpa using h2
  rcases D.ntypes.chiT_tg i k v hk with h | h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩
    rw [zpow_one, tameAnyFix_map_primeToPart]
    exact hval _ h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩
    rw [zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

end GlobalTheory.TypeLeaf
