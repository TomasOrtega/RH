import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open IsLocalRing

/- English proof (translation)
Introduce `C D _ _ _ φ hφ`. It suffices to establish `key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n → Module.length D (D ⧸ I.map φ) ≤ n by`. Introduce `I`. Consider the cases of `h : Module.length C (C ⧸ I) with`. Consider the case `top => exact le_top`.

Consider the case `coe n => exact key n I h`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `I hI`.

Establish `hs : Subsingleton (C ⧸ I)` using `Module.length_eq_zero_iff.mp (by exact_mod_cast hI)`. Establish `hItop : I = ⊤` using `Ideal.Quotient.subsingleton_iff.mp hs`. Substitute `hItop` using the available equality. Rewrite using `[Ideal.map_top]`. Establish `: Subsingleton (D ⧸ (⊤ : Ideal D))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`.

Simplify using `[Module.length_eq_zero]`. Consider the case `succ n ih`. Introduce `I hI`. Establish `hfin : IsFiniteLength C (C ⧸ I)` using `Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)`. Establish `: IsArtinian C (C ⧸ I)` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2`.

Establish `: Nontrivial (C ⧸ I)` using `Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)`. Establish `: IsAtomic (Submodule C (C ⧸ I))` using `isAtomic_of_orderBot_wellFounded_lt wellFounded_lt`. Take `⟨N, hN, -⟩` from `(eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot`. Establish `hNs : IsSimpleModule C N` using `isSimpleModule_iff_isAtom.mpr hN`. Establish `hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N)` using `Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)`.

Rewrite `hlen` using `[Module.length_eq_one (R := C) (M := N), hI]`. Establish `hq : Module.length C ((C ⧸ I) ⧸ N) = n`. Establish `hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤`. Introduce `h`. Rewrite `hlen` using `[h, add_top]`.

Conclude with `ENat.natCast_ne_top _ hlen`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.mp hx`. Rewrite `hlen`, the goal using `[← hk]`. Normalize the coercions in `at hlen ⊢`. Use linear arithmetic over natural numbers and integers.

Take `⟨v, hvN, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hN.1`. Establish `hspan : Submodule.span C {v} = N` using `(hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left (by simpa using hv0)`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Use `set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def`. Establish `hII' : I ≤ I'`.

Introduce `x hx`. Use `show Submodule.mkQ I x ∈ N`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]`. Conclude with `N.zero_mem`. Establish `hI'N : Submodule.map (Submodule.mkQ I) I' = N` using `Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N`.

Establish `hlenI' : Module.length C (C ⧸ I') = n`. Rewrite using `[← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]`. Establish `ih'` using `ih I' hlenI'`. Use `set m : Ideal C := Module.annihilator C N`. Establish `hm : m.IsMaximal` using `IsSimpleModule.annihilator_isMaximal`.

Establish `hmc : ∀ x ∈ m, x * c ∈ I`. Introduce `x hx`. Establish `h1` using `Module.mem_annihilator.mp hx ⟨_, hvN⟩`. Establish `h2 : x • (Ideal.Quotient.mk I c) = 0` using `congrArg Subtype.val h1`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul]`.

Simplify `h2` using `[Algebra.smul_def]`. Establish `hI'le : I' ≤ I ⊔ Ideal.span {c}`. Introduce `x hx`. Establish `hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c}` using `hspan ▸ hx`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp hx'`.

Establish `hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c)`. Rewrite using `[map_mul]`. Simplify `ha.symm` using `[Algebra.smul_def]`. Establish `hd : x - a * c ∈ I` using `Ideal.Quotient.eq.mp hxa`. Rewrite using `[show x = (x - a * c) + a * c by ring]`.

Conclude with `Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))`. Use `set J : Ideal D := I.map φ`. Use `set J' : Ideal D := I'.map φ`. Establish `hJJ' : J ≤ J'` using `Ideal.map_mono hII'`. Establish `hJ'le : J' ≤ J ⊔ Ideal.span {φ c}`.

Combine the equalities or inequalities in the displayed calculation. Use `set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)`. Use `set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'`. Establish `hK : K ≤ Submodule.span D {w}`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Take `⟨p, hp, q, hq', rfl⟩` from `Submodule.mem_sup.mp (hJ'le hy)`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp hq'`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp, zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]`. Conclude with `Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)`. Establish `hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J')`.

Rewrite using `[Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]`. Establish `hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]`.

Conclude with `Ideal.mem_map_of_mem φ (hmc x hx)`. Establish `hKle1 : Module.length D K ≤ 1`. Break down `hφ m hm with htop | hle` into its components or cases. Establish `hw : w = 0`. Establish `h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w)` using `hmX (htop ▸ Submodule.mem_top)`.

Simplify using `using h1`. Establish `hK0 : K = ⊥` using `le_bot_iff.mp (hK.trans (by simp [hw]))`. Rewrite using `[hK0, Module.length_bot]`. Conclude with `zero_le`. Establish `h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w)` using `hle.trans hmX`.

Set `f` to `(maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1`. Establish `hrange : LinearMap.range f = Submodule.span D {w}`. Rewrite using `[Submodule.range_liftQ, LinearMap.range_toSpanSingleton]`. Establish `: IsSimpleModule D (D ⧸ maximalIdeal D)` using `isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem LengthMapIdealLe.proof : LengthMapIdealLe.Statement.{u} := by
  intro C D _ _ _ φ hφ
  suffices key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n →
      Module.length D (D ⧸ I.map φ) ≤ n by
    intro I
    cases h : Module.length C (C ⧸ I) with
    | top => exact le_top
    | coe n => exact key n I h
  intro n
  induction n with
  | zero =>
    intro I hI
    have hs : Subsingleton (C ⧸ I) := Module.length_eq_zero_iff.mp (by exact_mod_cast hI)
    have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    subst hItop
    rw [Ideal.map_top]
    have : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro I hI
    have hfin : IsFiniteLength C (C ⧸ I) :=
      Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)
    have : IsArtinian C (C ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have : Nontrivial (C ⧸ I) :=
      Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule C (C ⧸ I)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot
    have hNs : IsSimpleModule C N := isSimpleModule_iff_isAtom.mpr hN

    have hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one (R := C) (M := N), hI] at hlen
    have hq : Module.length C ((C ⧸ I) ⧸ N) = n := by
      have hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top] at hlen
        exact ENat.natCast_ne_top _ hlen
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hk] at hlen ⊢
      norm_cast at hlen ⊢
      omega

    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN.1
    have hspan : Submodule.span C {v} = N :=
      (hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left
        (by simpa using hv0)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v

    set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def
    have hII' : I ≤ I' := by
      intro x hx
      show Submodule.mkQ I x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    have hI'N : Submodule.map (Submodule.mkQ I) I' = N :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N
    have hlenI' : Module.length C (C ⧸ I') = n := by
      rw [← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]
    have ih' := ih I' hlenI'

    set m : Ideal C := Module.annihilator C N
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmc : ∀ x ∈ m, x * c ∈ I := by
      intro x hx
      have h1 := Module.mem_annihilator.mp hx ⟨_, hvN⟩
      have h2 : x • (Ideal.Quotient.mk I c) = 0 := congrArg Subtype.val h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      simpa [Algebra.smul_def] using h2

    have hI'le : I' ≤ I ⊔ Ideal.span {c} := by
      intro x hx
      have hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c} := hspan ▸ hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
      have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c) := by
        rw [map_mul]
        simpa [Algebra.smul_def] using ha.symm
      have hd : x - a * c ∈ I := Ideal.Quotient.eq.mp hxa
      rw [show x = (x - a * c) + a * c by ring]
      exact Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))

    set J : Ideal D := I.map φ
    set J' : Ideal D := I'.map φ
    have hJJ' : J ≤ J' := Ideal.map_mono hII'
    have hJ'le : J' ≤ J ⊔ Ideal.span {φ c} := by
      calc J' ≤ (I ⊔ Ideal.span {c}).map φ := Ideal.map_mono hI'le
        _ = J ⊔ Ideal.span {φ c} := by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)
    set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'
    have hK : K ≤ Submodule.span D {w} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, q, hq', rfl⟩ := Submodule.mem_sup.mp (hJ'le hy)
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp,
        zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)
    have hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J') := by
      rw [Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]

    have hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem φ (hmc x hx)
    have hKle1 : Module.length D K ≤ 1 := by
      rcases hφ m hm with htop | hle
      · have hw : w = 0 := by
          have h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
            hmX (htop ▸ Submodule.mem_top)
          simpa using h1
        have hK0 : K = ⊥ := le_bot_iff.mp (hK.trans (by simp [hw]))
        rw [hK0, Module.length_bot]
        exact zero_le
      · have h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
          hle.trans hmX
        let f := (maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1
        have hrange : LinearMap.range f = Submodule.span D {w} := by
          rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
        have : IsSimpleModule D (D ⧸ maximalIdeal D) :=
          isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        calc Module.length D K ≤ Module.length D (Submodule.span D {w}) :=
              Module.length_le_of_injective (Submodule.inclusion hK) (Submodule.inclusion_injective hK)
          _ = Module.length D (LinearMap.range f) := by rw [hrange]
          _ ≤ Module.length D (D ⧸ maximalIdeal D) :=
              Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          _ = 1 := Module.length_eq_one _ _
    calc Module.length D (D ⧸ I.map φ) = Module.length D K + Module.length D (D ⧸ J') := hlenD
      _ ≤ 1 + n := add_le_add hKle1 ih'
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

end GroundTheory.Heights₂.Heights.NumbersDVR
