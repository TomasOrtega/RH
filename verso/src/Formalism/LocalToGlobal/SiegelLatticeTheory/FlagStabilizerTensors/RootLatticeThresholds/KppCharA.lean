import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW

variable {D : D7} (X : HidaSetting D)

abbrev wK (kv : Σ k : Fin 2, D.nd.PlG k) : HeightOneSpectrum (𝓞 X.B.I.E) := wB X (D.naut.plGw kv.1 kv.2)

/- English proof (translation)
Rewrite using `[card_wB, card_res_host]`.
-/
theorem card_wK (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wK X kv).asIdeal) = D.host.g kv.1 := by
  rw [card_wB, card_res_host]

/- English proof (translation)
The claim follows from `Nat.card_congr (Ideal.quotientEquiv (wc I w).asIdeal w.asIdeal (sigO I) (Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal).symm).toEquiv`.
-/
theorem card_wc {I : AutInst} (w : HeightOneSpectrum (𝓞 I.E)) :
    Nat.card (𝓞 I.E ⧸ (wc I w).asIdeal) = Nat.card (𝓞 I.E ⧸ w.asIdeal) :=
  Nat.card_congr (Ideal.quotientEquiv (wc I w).asIdeal w.asIdeal (sigO I)
    (Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal).symm).toEquiv

/- English proof (translation)
Rewrite using `[card_wc, card_wK]`.
-/
theorem card_wKc (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wc X.B.I (wK X kv)).asIdeal) = D.host.g kv.1 := by
  rw [card_wc, card_wK]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_wB (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E) :
    a ∈ (wB X w).asIdeal ↔ RingOfIntegers.mapRingEquiv X.ιE a ∈ w.asIdeal := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_wB, map_natCast]`. Conclude with `D.naut.plGw_over kv.1 kv.2`.
-/
theorem gk_mem (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
  rw [mem_wB, map_natCast]; exact D.naut.plGw_over kv.1 kv.2

/- English proof (translation)
The claim follows from `natCast_mem_wc X.B.I (gk_mem X kv)`.
-/
theorem gk_mem_c (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
  natCast_mem_wc X.B.I (gk_mem X kv)

/- English proof (translation)
Establish `hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)`. Establish `h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`. Simplify using `using h'.map (Int.castRingHom (𝓞 X.B.I.E))`. Take `⟨a, b, hab⟩` from `hcop`. Use `P.add_mem (P.mul_mem_left a h0) (P.mul_mem_left b h1)` as an intermediate fact.

Rewrite `this` using `[hab]`. Conclude with `hP ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem not_both (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ∈ P)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨a, b, hab⟩ := hcop
  have := P.add_mem (P.mul_mem_left a h0) (P.mul_mem_left b h1)
  rw [hab] at this
  exact hP ((Ideal.eq_top_iff_one _).2 this)

/- English proof (translation)
Apply the tactic sequence `fin_cases k <;> fin_cases k'`. Conclude with `hk rfl`. Conclude with `not_both X P hP h0 h1`. Conclude with `not_both X P hP h1 h0`. Conclude with `hk rfl`.
-/
theorem not_both' (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) {k k' : Fin 2} (hk : k ≠ k')
    (h0 : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) (h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  fin_cases k <;> fin_cases k'
  · exact hk rfl
  · exact not_both X P hP h0 h1
  · exact not_both X P hP h1 h0
  · exact hk rfl

/- English proof (translation)
Rewrite using `[X.g_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g_eq_cast : ((X.B.g : ℕ) : 𝓞 X.B.I.E) = ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
  rw [X.g_eq]; push_cast; ring

/- English proof (translation)
Rewrite `h` using `[g_eq_cast]`. Break down `hP.mem_or_mem h with h | h` into its components or cases. Use `exacts [⟨0, h⟩, ⟨1, h⟩]`.
-/
theorem gk_of_g {P : Ideal (𝓞 X.B.I.E)} (hP : P.IsPrime) (h : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast] at h
  rcases hP.mem_or_mem h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

/- English proof (translation)
Rewrite using `[g_eq_cast]`. Use `fin_cases k`. Conclude with `P.mul_mem_right _ h`. Conclude with `P.mul_mem_left _ h`.
-/
theorem g_mem_of_gk {P : Ideal (𝓞 X.B.I.E)} {k : Fin 2} (h : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast]
  fin_cases k
  · exact P.mul_mem_right _ h
  · exact P.mul_mem_left _ h

/- English proof (translation)
Establish `hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X P).asIdeal` using `by show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hP`. Take `⟨v, hv | hv⟩` from `cover X k (toH X P) hwH`. Conclude with `⟨v, Or.inl (by rw [← wB_toH X P, hv])⟩`.

Conclude with `⟨v, Or.inr (by rw [← wB_toH X P, hv, wB_conjH X])⟩`.
-/
theorem over_gk (P : HeightOneSpectrum (𝓞 X.B.I.E)) (k : Fin 2) (hP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ v : D.nd.PlG k, P = wK X ⟨k, v⟩ ∨ P = wc X.B.I (wK X ⟨k, v⟩) := by
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X P).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [map_natCast]; exact hP
  obtain ⟨v, hv | hv⟩ := cover X k (toH X P) hwH
  · exact ⟨v, Or.inl (by rw [← wB_toH X P, hv])⟩
  · exact ⟨v, Or.inr (by rw [← wB_toH X P, hv, wB_conjH X])⟩

/- English proof (translation)
Take `⟨k, hk⟩` from `gk_of_g X P.isPrime hP`. Take `⟨v, hv⟩` from `over_gk X P k hk`. Conclude with `⟨⟨k, v⟩, hv⟩`.
-/
theorem over_g (P : HeightOneSpectrum (𝓞 X.B.I.E)) (hP : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ kv : Σ k : Fin 2, D.nd.PlG k, P = wK X kv ∨ P = wc X.B.I (wK X kv) := by
  obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
  obtain ⟨v, hv⟩ := over_gk X P k hk
  exact ⟨⟨k, v⟩, hv⟩

/- English proof (translation)
Use `HeightOneSpectrum.ext ?_` and prove the remaining obligations. Use extensionality with `a`. Take `⟨b, rfl⟩` from `(RingOfIntegers.mapRingEquiv X.ιE).surjective a`. Rewrite using `[← mem_wB, ← mem_wB, h]`.
-/
theorem wB_inj {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : wB X w = wB X w') : w = w' := by
  refine HeightOneSpectrum.ext ?_
  ext a
  obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv X.ιE).surjective a
  rw [← mem_wB, ← mem_wB, h]

/- English proof (translation)
Take `⟨k, v⟩` from `kv`. Take `⟨k', v'⟩` from `kv'`. Introduce `he`. Distinguish the cases in `hk : k = k'`. Substitute `hk` using the available equality.

Establish `hv : v ≠ v'` using `fun hv => h (by rw [hv])`. Conclude with `hv (D.naut.plGw_inj k (wB_inj X he))`. Establish `h0` using `gk_mem X ⟨k, v⟩`. Establish `h1` using `gk_mem X ⟨k', v'⟩`. Rewrite `h1` using `[← he]`.

Conclude with `not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1`.
-/
theorem wK_ne {kv kv' : Σ k : Fin 2, D.nd.PlG k} (h : kv ≠ kv') : wK X kv ≠ wK X kv' := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    have hv : v ≠ v' := fun hv => h (by rw [hv])
    exact hv (D.naut.plGw_inj k (wB_inj X he))
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

/- English proof (translation)
Take `⟨k, v⟩` from `kv`. Take `⟨k', v'⟩` from `kv'`. Introduce `he`. Distinguish the cases in `hk : k = k'`. Substitute `hk` using the available equality.

Rewrite `he` using `[show wc X.B.I (wK X ⟨k, v'⟩) = wB X (conjH (D.naut.plGw k v')) from (wB_conjH X _).symm]`. Establish `he'` using `wB_inj X he`. Apply `D.naut.plGw_nconj k v' v` to reduce the goal to its premises. Use `isConjPl_conjH X (D.naut.plGw k v')` as an intermediate fact. Rewrite `this` using `[← he']`.

Conclude with `this`. Establish `h0` using `gk_mem X ⟨k, v⟩`. Establish `h1` using `gk_mem_c X ⟨k', v'⟩`. Rewrite `h1` using `[← he]`. Conclude with `not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1`.
-/
theorem wK_ne_wc (kv kv' : Σ k : Fin 2, D.nd.PlG k) : wK X kv ≠ wc X.B.I (wK X kv') := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    rw [show wc X.B.I (wK X ⟨k, v'⟩) = wB X (conjH (D.naut.plGw k v')) from (wB_conjH X _).symm] at he
    have he' := wB_inj X he
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    rw [← he'] at this
    exact this
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem_c X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

/- English proof (translation)
Establish `hk : ∀ k : Fin 2, a ∈ Ideal.span {((D.host.g k : ℕ) : 𝓞 X.B.I.E)}`. Introduce `k`. Use `mem_span_of_all (D.host.g_prime k) (unram X k) fun P hPm hgP => ?_` and prove the remaining obligations. Set `P' : HeightOneSpectrum (𝓞 X.B.I.E)` to `⟨P, hPm.isPrime, fun hb => by`. Rewrite `hgP` using `[hb]`.

Conclude with `(by exact_mod_cast (D.host.g_prime k).ne_zero : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ≠ 0) ((Submodule.mem_bot _).1 hgP)⟩`. Conclude with `ha P' (g_mem_of_gk X hgP)`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 (hk 0)`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.1 (hk 1)`. Establish `hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)`.

Establish `h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`. Simplify using `using h'.map (Int.castRingHom (𝓞 X.B.I.E))`. Take `⟨α, β, hαβ⟩` from `hcop`. Use `⟨α * v + β * u, ?_⟩` and prove the remaining obligations. Rewrite using `[g_eq_cast]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hv, hu]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by ring`.
-/
theorem mem_g_of_all {a : 𝓞 X.B.I.E}
    (ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal) :
    ∃ c : 𝓞 X.B.I.E, a = ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c := by
  have hk : ∀ k : Fin 2, a ∈ Ideal.span {((D.host.g k : ℕ) : 𝓞 X.B.I.E)} := by
    intro k
    refine mem_span_of_all (D.host.g_prime k) (unram X k) fun P hPm hgP => ?_
    let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
      rw [hb] at hgP
      exact (by exact_mod_cast (D.host.g_prime k).ne_zero : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ≠ 0)
        ((Submodule.mem_bot _).1 hgP)⟩
    exact ha P' (g_mem_of_gk X hgP)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hk 0)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hk 1)
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨α, β, hαβ⟩ := hcop
  refine ⟨α * v + β * u, ?_⟩
  rw [g_eq_cast]
  calc a = (α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) + β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) * a := by rw [hαβ, one_mul]
    _ = α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * (v * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) +
        β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) * (u * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E)) := by
          rw [hv, hu]; ring
    _ = _ := by ring

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 X.B.I.E))` to `Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 0) ∪ Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 1)`. Establish `hS : S.Finite` using `(Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 0)).union (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 1))`. Establish `: Finite S` using `hS.to_subtype`. Establish `hcop : Pairwise (Function.onFun IsCoprime fun P : S => (P.1).asIdeal)`. Introduce `P Q hPQ`.

Rewrite using `[Function.onFun, Ideal.isCoprime_iff_sup_eq]`. Use `Ideal.IsMaximal.coprime_of_ne (P.1).isMaximal (Q.1).isMaximal fun h => hPQ ?_` and prove the remaining obligations. Conclude with `Subtype.ext (HeightOneSpectrum.ext h)`. Take `⟨ε, hε⟩` from `Ideal.exists_forall_sub_mem_ideal hcop fun P => if P.1 = wK X kv then 1 else 0`. Establish `hmem : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ∈ S`.

Introduce `P hP`. Take `⟨k, hk⟩` from `gk_of_g X P.isPrime hP`. Use `fin_cases k`. Conclude with `Or.inl hk`. Conclude with `Or.inr hk`.

Use `⟨ε, ?_, fun P hP hne => ?_⟩` and prove the remaining obligations. Use `hε ⟨wK X kv, hmem _ (g_mem_of_gk X (gk_mem X kv))⟩` as an intermediate fact. Simplify using `using this`. Use `hε ⟨P, hmem P hP⟩` as an intermediate fact. Simplify using `only [if_neg hne, sub_zero] at this`.

Conclude with `this`.
-/
theorem exists_eps (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ε : 𝓞 X.B.I.E, ε - 1 ∈ (wK X kv).asIdeal ∧
      ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 X.B.I.E)) :=
    Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 0) ∪ Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 1)
  have hS : S.Finite := (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 0)).union
    (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 1))
  have : Finite S := hS.to_subtype
  have hcop : Pairwise (Function.onFun IsCoprime fun P : S => (P.1).asIdeal) := by
    intro P Q hPQ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (P.1).isMaximal (Q.1).isMaximal fun h => hPQ ?_
    exact Subtype.ext (HeightOneSpectrum.ext h)
  obtain ⟨ε, hε⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun P => if P.1 = wK X kv then 1 else 0
  have hmem : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ∈ S := by
    intro P hP
    obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨ε, ?_, fun P hP hne => ?_⟩
  · have := hε ⟨wK X kv, hmem _ (g_mem_of_gk X (gk_mem X kv))⟩
    simpa using this
  · have := hε ⟨P, hmem P hP⟩
    simp only [if_neg hne, sub_zero] at this
    exact this

/- English proof (translation)
Use `mem_span_of_all (D.host.g_prime k') (unram X k') fun P hPm hgP => ?_` and prove the remaining obligations. Set `P' : HeightOneSpectrum (𝓞 X.B.I.E)` to `⟨P, hPm.isPrime, fun hb => by`. Rewrite `hgP` using `[hb]`. Conclude with `(by exact_mod_cast (D.host.g_prime k').ne_zero : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ≠ 0) ((Submodule.mem_bot _).1 hgP)⟩`. Use `hε P' (g_mem_of_gk X hgP) fun he => ?_` and prove the remaining obligations.

Establish `h0` using `gk_mem X kv`. Establish `h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal` using `by rw [← he]; exact hgP`. Conclude with `not_both' X _ (wK X kv).isPrime.ne_top hk h1 h0`.
-/
theorem eps_other (kv : Σ k : Fin 2, D.nd.PlG k) {ε : 𝓞 X.B.I.E}
    (hε : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (k' : Fin 2) (hk : k' ≠ kv.1) : ε ∈ Ideal.span {((D.host.g k' : ℕ) : 𝓞 X.B.I.E)} := by
  refine mem_span_of_all (D.host.g_prime k') (unram X k') fun P hPm hgP => ?_
  let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
    rw [hb] at hgP
    exact (by exact_mod_cast (D.host.g_prime k').ne_zero : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ≠ 0)
      ((Submodule.mem_bot _).1 hgP)⟩
  refine hε P' (g_mem_of_gk X hgP) fun he => ?_
  have h0 := gk_mem X kv
  have h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by rw [← he]; exact hgP
  exact not_both' X _ (wK X kv).isPrime.ne_top hk h1 h0

end Formalism.L2.SG.Pf.KppChar
