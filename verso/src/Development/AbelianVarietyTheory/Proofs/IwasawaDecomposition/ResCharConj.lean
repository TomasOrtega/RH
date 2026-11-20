import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsFurther

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TwFin

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IsolatedTheoremFour.main`. Consider the case `exact _root_.GlobalTheory.IsolatedTheoremFour.main`. Consider the case `(apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)`.
-/
theorem exists_over {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFour.main
  | exact _root_.GlobalTheory.IsolatedTheoremFour.main
  | (apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)

/- English proof (translation)
Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hl` after adjusting the coercions. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Use `show v.asIdeal ∣ _`.

Rewrite using `[Ideal.dvd_span_singleton]`. Conclude with `hv`.
-/
theorem finite_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

/- English proof (translation)
Introduce `h`. Take `⟨v, hv⟩` from `exists_over (K := H.E) hp`. Establish `hu : ψ.UnrAt v`. Assume the negation of the conclusion as `hn`. Take `⟨-, hq, -, hnS⟩` from `hψ.2.2.2 v hn`.

Use `Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv` as an intermediate fact. Conclude with `hnS (this ▸ hS)`. Establish `h1` using `(hδ.ine v hv 1).1 fun x hx => by`. Establish `h2 : (δ * ψ).loc v x = 1` using `by rw [h, HChar.loc_one]`. Rewrite `h2` using `[HChar.loc_mul, hu x hx, mul_one]`.

Rewrite using `[h2, one_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mul_ne_one {R : Ranks} {H : Formalism.BasicNotions.Host R} {S : Set ℕ} {p : ℕ} {δ ψ : HChar H.E} (hp : p.Prime) (hS : p ∈ S)
    (hδ : IsDelta (H := H) p δ) (hψ : Chr.IsTwist H S ψ) : δ * ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over (K := H.E) hp
  have hu : ψ.UnrAt v := by
    by_contra hn
    obtain ⟨-, hq, -, hnS⟩ := hψ.2.2.2 v hn
    have := Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv
    exact hnS (this ▸ hS)
  have h1 := (hδ.ine v hv 1).1 fun x hx => by
    have h2 : (δ * ψ).loc v x = 1 := by rw [h, HChar.loc_one]
    rw [HChar.loc_mul, hu x hx, mul_one] at h2
    rw [h2, one_pow]
  omega

/- English proof (translation)
Use `Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_mem _) ?_` and prove the remaining obligations. Establish `h` using `(Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2 (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)`. Rewrite `h` using `[pow_one]`. Conclude with `h`.
-/
theorem resChar_conj (B : Base) (w : B.places.Pl) : B.places.resChar (B.places.conj w) = B.places.resChar w := by
  refine Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) ?_
  have h := (Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2
    (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)
  rw [pow_one] at h
  exact h

/- English proof (translation)
Use `((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩`.
-/
theorem finite_pl (B : Base) (s : Finset ℕ) : {w : B.places.Pl | B.places.resChar w ∈ s}.Finite := by
  refine ((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion
    fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  exact ⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩

/- English proof (translation)
Introduce `B f T`. Use `⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩` and prove the remaining obligations. Establish `h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite` using `Set.toFinite _`. Use `(h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_` and prove the remaining obligations. Introduce and unpack `ξ (h | ⟨w, rfl⟩)`.

Conclude with `Or.inl h`. Distinguish the cases in `hw : B.places.resChar w ∈ T.pl`. Conclude with `Or.inr ⟨w, hw, rfl⟩`. Use `left`. Unfold `TwDat.xiTw`.

Rewrite using `[(T.off w hw).1, mul_one]`. Use `split_ifs`. Conclude with `Or.inr (Or.inr rfl)`. Conclude with `Or.inr (Or.inl rfl)`. Unfold `TwDat.xiTw split_ifs`.

Conclude with `mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)`. Conclude with `mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)`. Unfold `TwDat.xiTw`. Rewrite using `[resChar_conj, (T.conj w).1]`.
-/
theorem tw_fin : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), (T.set f).Finite ∧ (∀ w, T.xiTw f w ≠ 1) ∧ (∀ w, T.xiTw f (B.places.conj w) = T.xiTw f w) ∧ {w : B.places.Pl | B.places.resChar w ∈ T.pl}.Finite := by
  intro B f T
  refine ⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩
  · have h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite := Set.toFinite _
    refine (h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_
    rintro ξ (h | ⟨w, rfl⟩)
    · exact Or.inl h
    · by_cases hw : B.places.resChar w ∈ T.pl
      · exact Or.inr ⟨w, hw, rfl⟩
      · left
        unfold TwDat.xiTw
        rw [(T.off w hw).1, mul_one]
        split_ifs
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  · unfold TwDat.xiTw
    split_ifs
    · exact mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)
    · exact mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)
  · unfold TwDat.xiTw
    rw [resChar_conj, (T.conj w).1]

end GlobalTheory.Mem.Top.TwFin
