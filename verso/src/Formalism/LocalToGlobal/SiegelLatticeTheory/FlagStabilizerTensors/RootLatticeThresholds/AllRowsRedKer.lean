import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRedKer

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.MainNotions.BridgeLemma

variable {D : D7}

def sigH (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigH_coe (a : 𝓞 D.host.E) : ((sigH D a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := rfl

def conjH (w : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (sigH D)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (sigH D).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

/- English proof (translation)
Take `⟨x, rfl⟩` from `X.ιE.surjective y`. Rewrite using `[← X.ιE_conj, ← X.ιE_conj, star_star]`.
-/
theorem conj_conj (X : HidaSetting D) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  obtain ⟨x, rfl⟩ := X.ιE.surjective y
  rw [← X.ιE_conj, ← X.ιE_conj, star_star]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[sigH_coe, sigH_coe]`. Conclude with `conj_conj X _`.
-/
theorem sigH_sigH (X : HidaSetting D) (a : 𝓞 D.host.E) : sigH D (sigH D a) = a := by
  apply RingOfIntegers.ext
  rw [sigH_coe, sigH_coe]
  exact conj_conj X _

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use `show (w.asIdeal.comap (sigH D)).comap (sigH D) = w.asIdeal`. Use extensionality with `a`. Simplify using `only [Ideal.mem_comap]`. Rewrite using `[sigH_sigH X]`.
-/
theorem conjH_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : conjH (conjH w) = w := by
  apply HeightOneSpectrum.ext
  show (w.asIdeal.comap (sigH D)).comap (sigH D) = w.asIdeal
  ext a
  simp only [Ideal.mem_comap]
  rw [sigH_sigH X]

/- English proof (translation)
Introduce `x y hxy`. Establish `hs : sigH D y = x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[sigH_coe, hxy, conj_conj X]`. Use `show x ∈ w.asIdeal ↔ sigH D y ∈ w.asIdeal`.

Rewrite using `[hs]`.
-/
theorem isConjPl_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : IsConjPl D.host w (conjH w) := by
  intro x y hxy
  have hs : sigH D y = x := by
    apply RingOfIntegers.ext
    rw [sigH_coe, hxy, conj_conj X]
  show x ∈ w.asIdeal ↔ sigH D y ∈ w.asIdeal
  rw [hs]

/- English proof (translation)
Use `show sigH D (p : 𝓞 D.host.E) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `h`.
-/
theorem natCast_mem_conjH {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ} (h : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    (p : 𝓞 D.host.E) ∈ (conjH w).asIdeal := by
  show sigH D (p : 𝓞 D.host.E) ∈ w.asIdeal
  rw [map_natCast]
  exact h

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[mem_wc]`. Simplify using `only [wB, conjH, Ideal.mem_comap]`. Establish `hc : sigH D (RingOfIntegers.mapRingEquiv X.ιE a) = RingOfIntegers.mapRingEquiv X.ιE (sigO X.B.I a)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[sigH_coe]`. Simplify using `[RingOfIntegers.mapRingEquiv, sigO_coe, X.ιE_conj]`. Rewrite using `[hc]`.
-/
theorem wB_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wB X (conjH w) = wc X.B.I (wB X w) := by
  apply HeightOneSpectrum.ext
  ext a
  rw [mem_wc]
  simp only [wB, conjH, Ideal.mem_comap]
  have hc : sigH D (RingOfIntegers.mapRingEquiv X.ιE a) =
      RingOfIntegers.mapRingEquiv X.ιE (sigO X.B.I a) := by
    apply RingOfIntegers.ext
    rw [sigH_coe]
    simp [RingOfIntegers.mapRingEquiv, sigO_coe, X.ιE_conj]
  rw [hc]

/- English proof (translation)
Use `haveI := D.host.galois`. Rewrite using `[← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv, Formalism.HC.Frame.natCard_GG]`. Simplify using `only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_cmField (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv, Formalism.HC.Frame.natCard_GG]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

/- English proof (translation)
Establish `hp` using `D.host.g_prime k`. Use `set A : Set (HeightOneSpectrum (𝓞 D.host.E)) := Set.range (D.naut.plGw k) ∪ Set.range (fun v => conjH (D.naut.plGw k v)) with hA`. Use `set T : Set (HeightOneSpectrum (𝓞 D.host.E)) := placesOver D.host.E (D.host.g k) with hT`. Establish `hAT : A ⊆ T`. Introduce and unpack `_ (⟨v, rfl⟩ | ⟨v, rfl⟩)`.

Conclude with `D.naut.plGw_over k v`. Conclude with `natCast_mem_conjH (D.naut.plGw_over k v)`. Establish `hTfin : T.Finite` using `finite_plOver D.host.E hp`. Establish `hinj2 : Function.Injective (fun v => conjH (D.naut.plGw k v))`. Introduce `v v' h`.

Apply `D.naut.plGw_inj k` to reduce the goal to its premises. Use `congrArg conjH h` as an intermediate fact. Simplify `this` using `only [conjH_conjH X]`. Establish `hdisj : Disjoint (Set.range (D.naut.plGw k)) (Set.range (fun v => conjH (D.naut.plGw k v)))`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `_ ⟨v, rfl⟩ ⟨v', hv'⟩`. Apply `D.naut.plGw_nconj k v' v` to reduce the goal to its premises. Use `isConjPl_conjH X (D.naut.plGw k v')` as an intermediate fact. Establish `hv'' : conjH (D.naut.plGw k v') = D.naut.plGw k v` using `hv'`. Rewrite `this` using `[hv'']`.

Conclude with `this`. Establish `hcA : A.ncard = 2 * D.R.f`. Rewrite using `[hA, Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _), Set.ncard_range_of_injective (D.naut.plGw_inj k), Set.ncard_range_of_injective hinj2, Nat.card_eq_fintype_card, D.nd.card_PlG k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcT : T.ncard = 2 * D.R.f` using `by rw [hT, D.nd.g_split k, finrank_cmField]`.

Establish `hEq : A = T` using `Set.eq_of_subset_of_ncard_le hAT (by rw [hcA, hcT]) hTfin`. Establish `: w ∈ A` using `by rw [hEq]; exact hw`. Break down `this with ⟨v, rfl⟩ | ⟨v, rfl⟩` into its components or cases. Conclude with `⟨v, Or.inl rfl⟩`. Conclude with `⟨v, Or.inr rfl⟩`.
-/
theorem cover (X : HidaSetting D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = conjH (D.naut.plGw k v) := by
  have hp := D.host.g_prime k
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    Set.range (D.naut.plGw k) ∪ Set.range (fun v => conjH (D.naut.plGw k v)) with hA
  set T : Set (HeightOneSpectrum (𝓞 D.host.E)) := placesOver D.host.E (D.host.g k) with hT
  have hAT : A ⊆ T := by
    rintro _ (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact D.naut.plGw_over k v
    · exact natCast_mem_conjH (D.naut.plGw_over k v)
  have hTfin : T.Finite := finite_plOver D.host.E hp
  have hinj2 : Function.Injective (fun v => conjH (D.naut.plGw k v)) := by
    intro v v' h
    apply D.naut.plGw_inj k
    have := congrArg conjH h
    simpa only [conjH_conjH X] using this
  have hdisj : Disjoint (Set.range (D.naut.plGw k)) (Set.range (fun v => conjH (D.naut.plGw k v))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨v', hv'⟩
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    have hv'' : conjH (D.naut.plGw k v') = D.naut.plGw k v := hv'
    rw [hv''] at this
    exact this
  have hcA : A.ncard = 2 * D.R.f := by
    rw [hA, Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      Set.ncard_range_of_injective (D.naut.plGw_inj k), Set.ncard_range_of_injective hinj2,
      Nat.card_eq_fintype_card, D.nd.card_PlG k]
    ring
  have hcT : T.ncard = 2 * D.R.f := by rw [hT, D.nd.g_split k, finrank_cmField]
  have hEq : A = T := Set.eq_of_subset_of_ncard_le hAT (by rw [hcA, hcT]) hTfin
  have : w ∈ A := by rw [hEq]; exact hw
  rcases this with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr rfl⟩

/- English proof (translation)
Establish `hp` using `D.host.g_prime k`. Use `span_isMaximal hp` as an intermediate fact. Establish `hspl` using `splitsCompl_of_ncard D.host.E (D.host.g k) hp (by`. Rewrite using `[← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp, (injOn_asIdeal _ _).ncard_image]`. Conclude with `D.nd.g_split k)`.

Use `set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE`. Establish `hQm : (P.map e).IsMaximal` using `Ideal.map_isMaximal_of_equiv e`. Establish `hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e`. Use `Ideal.mem_map_of_mem e hgP` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Take `⟨-, hsq⟩` from `hspl _ hQm hgQ`. Introduce `h`. Apply `hsq` to reduce the goal to its premises. Use `Ideal.mem_map_of_mem e h` as an intermediate fact. Rewrite `this` using `[map_natCast, Ideal.map_pow]`. Then use the resulting hypothesis.
-/
theorem unram (X : HidaSetting D) (k : Fin 2) (P : Ideal (𝓞 X.B.I.E)) (hPm : P.IsMaximal)
    (hgP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have hQm : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
    have := Ideal.mem_map_of_mem e hgP
    rwa [map_natCast] at this
  obtain ⟨-, hsq⟩ := hspl _ hQm hgQ
  intro h
  apply hsq
  have := Ideal.mem_map_of_mem e h
  rwa [map_natCast, Ideal.map_pow] at this

def toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv X.ιE).symm
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).symm.surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[wB, toH, Ideal.mem_comap]`.
-/
theorem wB_toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : wB X (toH X w) = w := by
  apply HeightOneSpectrum.ext
  ext a
  simp [wB, toH, Ideal.mem_comap]

/- English proof (translation)
Introduce `x hx hred`. Establish `hp` using `D.host.g_prime k`. Establish `hA : ∀ v, ∀ y ∈ X.B.I.Lf, (X.B.I.fmat x - 1) *ᵥ y ∈ Lq X.B.I (wB X (D.naut.plGw k v))`. Introduce `v`. Establish `h0` using `(redMat_iff X _ _ x _).1 (hred v)`.

Conclude with `stepA X.B.I hp (by rw [card_wB, card_res_host]) hx h0`. Use `glue X.B.I hp (unram X k) hx fun w hw => ?_` and prove the remaining obligations. Establish `hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X w).asIdeal` using `by show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hw`.

Take `⟨v, hv | hv⟩` from `cover X k (toH X w) hwH`. Rewrite using `[← wB_toH X w, hv]`. Conclude with `hA v`. Rewrite using `[← wB_toH X w, hv, wB_conjH X]`. Conclude with `stepB X.B.I hx (hA v)`.
-/
theorem redKerP_holds (X : HidaSetting D) (k : Fin 2) : Formalism.L2.SG.AllRowsOf.RedKerP X k := by
  intro x hx hred
  have hp := D.host.g_prime k
  have hA : ∀ v, ∀ y ∈ X.B.I.Lf, (X.B.I.fmat x - 1) *ᵥ y ∈ Lq X.B.I (wB X (D.naut.plGw k v)) := by
    intro v
    have h0 := (redMat_iff X _ _ x _).1 (hred v)
    exact stepA X.B.I hp (by rw [card_wB, card_res_host]) hx h0
  refine glue X.B.I hp (unram X k) hx fun w hw => ?_
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X w).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [map_natCast]; exact hw
  obtain ⟨v, hv | hv⟩ := cover X k (toH X w) hwH
  · rw [← wB_toH X w, hv]
    exact hA v
  · rw [← wB_toH X w, hv, wB_conjH X]
    exact stepB X.B.I hx (hA v)

end Formalism.L2.SG.Pf.AllRowsRedKer
