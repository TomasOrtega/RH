import Mathlib
import Development.EtaleCohomology.EtaleSheaves.FibreIdem

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof

namespace UpperTheory.Cb.RestrictionHomomorphisms

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

private abbrev mI (A : Type) [CommRing A] [IsLocalRing A] (S : Type) [CommRing S] [Algebra A S] : Ideal S :=
  (IsLocalRing.maximalIdeal A).map (algebraMap A S)

/- English proof (translation)
Establish `h1 : Subalgebra.toSubmodule S = Submodule.map S.val.toLinearMap ⊤`. Rewrite using `[Submodule.map_top]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Use `show (s : K) ∈ IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S ↔ _`.

Rewrite using `[h1, ← Submodule.map_smul'', Ideal.smul_top_eq_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hys⟩`. Establish `hy' : y = s` using `Subtype.ext hys`. Substitute `hy'` using the available equality.

Conclude with `hy`. Introduce `h`. Conclude with `⟨s, h, rfl⟩`.
-/
private lemma mem_mS_iff (S : Subalgebra A K) (s : S) : (s : K) ∈ mS S ↔ s ∈ mI A S := by
  have h1 : Subalgebra.toSubmodule S = Submodule.map S.val.toLinearMap ⊤ := by
    rw [Submodule.map_top]
    ext x
    simp
  show (s : K) ∈ IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S ↔ _
  rw [h1, ← Submodule.map_smul'', Ideal.smul_top_eq_map]
  constructor
  · rintro ⟨y, hy, hys⟩
    have hy' : y = s := Subtype.ext hys
    subst hy'
    exact hy
  · intro h
    exact ⟨s, h, rfl⟩

/- English proof (translation)
Use `⟨⟨x.asIdeal.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩, ?_⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap _ (Ideal.map _ _) = _`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h]`.
-/
private lemma exists_q {S : Type} [CommRing S] (I : Ideal S) (x : PrimeSpectrum S) (h : I ≤ x.asIdeal) :
    ∃ q : PrimeSpectrum (S ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) q = x := by
  refine ⟨⟨x.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩, ?_⟩
  apply PrimeSpectrum.ext
  show Ideal.comap _ (Ideal.map _ _) = _
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr h]

/- English proof (translation)
Take `⟨u, hu, hW'⟩` from `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hW.preimage hg)`. Take `⟨e, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Use `⟨e, ?_, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu.eq, sub_self]`. Establish `h` using `Set.ext_iff.mp hW' q`.

Rewrite `h` using `[Set.mem_preimage]`. Rewrite using `[h, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`.
-/
private lemma idem_of_clopen {S : Type} [CommRing S] (I : Ideal S) {F : Type} [TopologicalSpace F]
    (g : PrimeSpectrum (S ⧸ I) → F) (hg : Continuous g) (W : Set F) (hW : IsClopen W) :
    ∃ e : S, e * e - e ∈ I ∧ ∀ q : PrimeSpectrum (S ⧸ I),
      g q ∈ W ↔ e ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal := by
  obtain ⟨u, hu, hW'⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hW.preimage hg)
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨e, ?_, fun q => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu.eq, sub_self]
  · have h := Set.ext_iff.mp hW' q
    rw [Set.mem_preimage] at h
    rw [h, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]

/- English proof (translation)
Establish `hcomp : (Subalgebra.inclusion hS).toRingHom.comp (algebraMap A S) = algebraMap A (AdjoinInv B t)` using `RingHom.ext fun _ => Subtype.ext rfl`. Establish `hle : mI A S ≤ (PrimeSpectrum.comap (Subalgebra.inclusion hS).toRingHom Q).asIdeal` using `by show Ideal.map _ _ ≤ Ideal.comap _ Q.asIdeal`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomp, ← Ideal.map_le_iff_le_comap]`. Conclude with `hQ`. Take `⟨q, hq⟩` from `exists_q (mI A S) _ hle`.

Use `⟨q, ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Introduce `s`. Prove the components needed by the constructor for the conclusion. Introduce `hs`.

Conclude with `⟨Subalgebra.inclusion hS s, hs, rfl⟩`. Introduce and unpack `⟨d, hd, hds⟩`. Establish `hd' : d = Subalgebra.inclusion hS s` using `Subtype.ext hds`. Rewrite `hd` using `[hd']`. Conclude with `hd`.

Rewrite using `[hq]`. Both sides reduce to the same expression.
-/
private lemma restr_ex (B : Subalgebra A K) (t : K) (S : Subalgebra A K) (hS : S ≤ AdjoinInv B t)
    (Q : PrimeSpectrum (AdjoinInv B t)) (hQ : mI A (AdjoinInv B t) ≤ Q.asIdeal) :
    ∃ q : PrimeSpectrum (S ⧸ mI A S), Restr B t Q S (PrimeSpectrum.comap (Ideal.Quotient.mk _) q) ∧
      ∀ s : S, s ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal ↔
        Subalgebra.inclusion hS s ∈ Q.asIdeal := by
  have hcomp : (Subalgebra.inclusion hS).toRingHom.comp (algebraMap A S) = algebraMap A (AdjoinInv B t) :=
    RingHom.ext fun _ => Subtype.ext rfl
  have hle : mI A S ≤ (PrimeSpectrum.comap (Subalgebra.inclusion hS).toRingHom Q).asIdeal := by
    show Ideal.map _ _ ≤ Ideal.comap _ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomp, ← Ideal.map_le_iff_le_comap]
    exact hQ
  obtain ⟨q, hq⟩ := exists_q (mI A S) _ hle
  refine ⟨q, ?_, fun s => ?_⟩
  · rw [hq]
    intro s
    constructor
    · intro hs
      exact ⟨Subalgebra.inclusion hS s, hs, rfl⟩
    · rintro ⟨d, hd, hds⟩
      have hd' : d = Subalgebra.inclusion hS s := Subtype.ext hds
      rw [hd'] at hd
      exact hd
  · rw [hq]
    rfl

/- English proof (translation)
Take `⟨eB, heB, hWB⟩` from `idem_of_clopen (mI A B) gB hgB W hW`. Take `⟨eC, heC, hWC⟩` from `idem_of_clopen (mI A C) gC hgC W hW`. Establish `hBD : B ≤ AdjoinInv B t` using `fun b hb => Algebra.subset_adjoin (Or.inl hb)`. Establish `hCD : C ≤ AdjoinInv B t`. Rewrite using `[hc.glue]`.

Conclude with `fun c hc' => Algebra.subset_adjoin (Or.inl hc')`. Establish `hmap : ∀ (S : Subalgebra A K) (h : S ≤ AdjoinInv B t) (s : S), s ∈ mI A S → Subalgebra.inclusion h s ∈ mI A (AdjoinInv B t)`. Introduce `S h s hs`. Establish `hcomp : (Subalgebra.inclusion h).toRingHom.comp (algebraMap A S) = algebraMap A (AdjoinInv B t)` using `RingHom.ext fun _ => Subtype.ext rfl`. Establish `h'` using `Ideal.mem_map_of_mem (Subalgebra.inclusion h).toRingHom hs`.

Rewrite `h'` using `[Ideal.map_map, hcomp]`. Conclude with `h'`. Establish `inn : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e ∈ mI A S → e ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal`. Introduce `S e q he`. Use `show Ideal.Quotient.mk (mI A S) e ∈ q.asIdeal`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 he]`. Conclude with `q.asIdeal.zero_mem`. Establish `notin : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e - 1 ∈ mI A S → e ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal`. Introduce `S e q he hq`. Apply `q.isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h0 : Ideal.Quotient.mk (mI A S) (e - 1) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 he`. Rewrite `h0` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[← h0]`. Conclude with `hq`.

Use `set a : AdjoinInv B t := Subalgebra.inclusion hBD eB with ha_def`. Use `set b : AdjoinInv B t := Subalgebra.inclusion hCD eC with hb_def`. Establish `ha : a * a - a ∈ mI A (AdjoinInv B t)`. Establish `h'` using `hmap B hBD _ heB`. Rewrite `h'` using `[map_sub, map_mul]`.

Conclude with `h'`. Establish `hb : b * b - b ∈ mI A (AdjoinInv B t)`. Establish `h'` using `hmap C hCD _ heC`. Rewrite `h'` using `[map_sub, map_mul]`. Conclude with `h'`.

Establish `hrad : a - b ∈ (mI A (AdjoinInv B t)).radical`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hPle, hP⟩`. Set `Q : PrimeSpectrum (AdjoinInv B t)` to `⟨P, hP⟩`. Take `⟨qB, hRB, hmB⟩` from `restr_ex B t B hBD Q hPle`.

Take `⟨qC, hRC, hmC⟩` from `restr_ex B t C hCD Q hPle`. Establish `hg` using `hov qB qC Q hRB hRC`. Establish `e1 : a ∈ P ↔ b ∈ P`. Establish `h1` using `hWB qB`. Establish `h2` using `hWC qC`.

Rewrite `h1` using `[hg, hmB]`. Rewrite `h2` using `[hmC]`. Conclude with `not_iff_not.mp (h1.symm.trans h2)`. Establish `ha' : a * (1 - a) ∈ P`. Establish `e : a * (1 - a) = -(a * a - a)` using `by ring`.

Rewrite using `[e]`. Conclude with `P.neg_mem (hPle ha)`. Establish `hb' : b * (1 - b) ∈ P`. Establish `e : b * (1 - b) = -(b * b - b)` using `by ring`. Rewrite using `[e]`.

Conclude with `P.neg_mem (hPle hb)`. Break down `hP.mem_or_mem ha' with h | h` into its components or cases. Conclude with `P.sub_mem h (e1.1 h)`. Establish `hb1 : 1 - b ∈ P`. Break down `hP.mem_or_mem hb' with h2 | h2` into its components or cases.

It suffices to derive a contradiction. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h3` using `P.add_mem (e1.2 h2) h`. Rewrite `h3` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `h2`. Establish `e : a - b = (1 - b) - (1 - a)` using `by ring`. Rewrite using `[e]`. Conclude with `P.sub_mem hb1 h`. Establish `hmem : a - b ∈ mI A (AdjoinInv B t)`.

Take `⟨n, hn⟩` from `hrad`. Use `set x := Ideal.Quotient.mk (mI A (AdjoinInv B t)) a`. Use `set y := Ideal.Quotient.mk (mI A (AdjoinInv B t)) b`. Establish `hx : x * x = x`. Rewrite using `[← sub_eq_zero, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ha`. Establish `hy : y * y = y`. Rewrite using `[← sub_eq_zero, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hb`. Establish `h3 : (x - y) ^ 3 = x - y`.

Take the linear combination `(x + 1 - 3 * y) * hx + (3 * x - y - 1) * hy`. Establish `hodd : ∀ k : ℕ, (x - y) ^ (2 * k + 1) = x - y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ih, ← pow_succ', h3]`. Establish `hzero : (x - y) ^ n = 0`. Rewrite using `[← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hn`.

Establish `hv : x - y = 0`. Rewrite using `[← hodd n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hzero, zero_mul]`. Rewrite `hv` using `[← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hv`. Use `⟨(eB : K), (eC : K), ⟨eB.2, eC.2, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(mem_mS_iff B (eB * eB - eB)).2 heB`. Conclude with `(mem_mS_iff C (eC * eC - eC)).2 heC`. Conclude with `(mem_mS_iff (AdjoinInv B t) (a - b)).2 hmem`. Introduce and unpack `⟨h1, h2⟩`. Establish `hB' : eB ∈ mI A B` using `(mem_mS_iff B eB).1 h1`.

Establish `hC' : eC ∈ mI A C` using `(mem_mS_iff C eC).1 h2`. Use extensionality with `w`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hw`. Break down `hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩` into its components or cases.

Conclude with `(hWB q).1 hw (inn eB q hB')`. Conclude with `(hWC q).1 hw (inn eC q hC')`. Introduce and unpack `⟨h1, h2⟩`. Establish `hB' : eB - 1 ∈ mI A B` using `(mem_mS_iff B (eB - 1)).1 h1`. Establish `hC' : eC - 1 ∈ mI A C` using `(mem_mS_iff C (eC - 1)).1 h2`.

Use extensionality with `w`. Simplify using `only [Set.mem_univ, iff_true]`. Break down `hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩` into its components or cases. Conclude with `(hWB q).2 (notin eB q hB')`. Conclude with `(hWC q).2 (notin eC q hC')`.
-/
private lemma pair_of_maps (B C : Subalgebra A K) (t : K) (hc : Charts B C t) {F : Type} [TopologicalSpace F]
    (gB : PrimeSpectrum (B ⧸ mI A B) → F) (gC : PrimeSpectrum (C ⧸ mI A C) → F)
    (hgB : Continuous gB) (hgC : Continuous gC)
    (hcov : ∀ w, (∃ q, gB q = w) ∨ ∃ q, gC q = w)
    (hov : ∀ (qB : PrimeSpectrum (B ⧸ mI A B)) (qC : PrimeSpectrum (C ⧸ mI A C)) (Q : PrimeSpectrum (AdjoinInv B t)),
      Restr B t Q B (PrimeSpectrum.comap (Ideal.Quotient.mk _) qB) →
      Restr B t Q C (PrimeSpectrum.comap (Ideal.Quotient.mk _) qC) → gB qB = gC qC)
    (W : Set F) (hW : IsClopen W) :
    ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ) := by
  obtain ⟨eB, heB, hWB⟩ := idem_of_clopen (mI A B) gB hgB W hW
  obtain ⟨eC, heC, hWC⟩ := idem_of_clopen (mI A C) gC hgC W hW
  have hBD : B ≤ AdjoinInv B t := fun b hb => Algebra.subset_adjoin (Or.inl hb)
  have hCD : C ≤ AdjoinInv B t := by
    rw [hc.glue]
    exact fun c hc' => Algebra.subset_adjoin (Or.inl hc')
  have hmap : ∀ (S : Subalgebra A K) (h : S ≤ AdjoinInv B t) (s : S), s ∈ mI A S →
      Subalgebra.inclusion h s ∈ mI A (AdjoinInv B t) := by
    intro S h s hs
    have hcomp : (Subalgebra.inclusion h).toRingHom.comp (algebraMap A S) = algebraMap A (AdjoinInv B t) :=
      RingHom.ext fun _ => Subtype.ext rfl
    have h' := Ideal.mem_map_of_mem (Subalgebra.inclusion h).toRingHom hs
    rw [Ideal.map_map, hcomp] at h'
    exact h'
  have inn : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e ∈ mI A S →
      e ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal := by
    intro S e q he
    show Ideal.Quotient.mk (mI A S) e ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 he]
    exact q.asIdeal.zero_mem
  have notin : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e - 1 ∈ mI A S →
      e ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal := by
    intro S e q he hq
    apply q.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h0 : Ideal.Quotient.mk (mI A S) (e - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 he
    rw [map_sub, map_one, sub_eq_zero] at h0
    rw [← h0]
    exact hq
  set a : AdjoinInv B t := Subalgebra.inclusion hBD eB with ha_def
  set b : AdjoinInv B t := Subalgebra.inclusion hCD eC with hb_def
  have ha : a * a - a ∈ mI A (AdjoinInv B t) := by
    have h' := hmap B hBD _ heB
    rw [map_sub, map_mul] at h'
    exact h'
  have hb : b * b - b ∈ mI A (AdjoinInv B t) := by
    have h' := hmap C hCD _ heC
    rw [map_sub, map_mul] at h'
    exact h'
  have hrad : a - b ∈ (mI A (AdjoinInv B t)).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hPle, hP⟩
    let Q : PrimeSpectrum (AdjoinInv B t) := ⟨P, hP⟩
    obtain ⟨qB, hRB, hmB⟩ := restr_ex B t B hBD Q hPle
    obtain ⟨qC, hRC, hmC⟩ := restr_ex B t C hCD Q hPle
    have hg := hov qB qC Q hRB hRC
    have e1 : a ∈ P ↔ b ∈ P := by
      have h1 := hWB qB
      have h2 := hWC qC
      rw [hg, hmB] at h1
      rw [hmC] at h2
      exact not_iff_not.mp (h1.symm.trans h2)
    have ha' : a * (1 - a) ∈ P := by
      have e : a * (1 - a) = -(a * a - a) := by ring
      rw [e]
      exact P.neg_mem (hPle ha)
    have hb' : b * (1 - b) ∈ P := by
      have e : b * (1 - b) = -(b * b - b) := by ring
      rw [e]
      exact P.neg_mem (hPle hb)
    rcases hP.mem_or_mem ha' with h | h
    · exact P.sub_mem h (e1.1 h)
    · have hb1 : 1 - b ∈ P := by
        rcases hP.mem_or_mem hb' with h2 | h2
        · exfalso
          apply hP.ne_top
          rw [Ideal.eq_top_iff_one]
          have h3 := P.add_mem (e1.2 h2) h
          rwa [add_sub_cancel] at h3
        · exact h2
      have e : a - b = (1 - b) - (1 - a) := by ring
      rw [e]
      exact P.sub_mem hb1 h
  have hmem : a - b ∈ mI A (AdjoinInv B t) := by
    obtain ⟨n, hn⟩ := hrad
    set x := Ideal.Quotient.mk (mI A (AdjoinInv B t)) a
    set y := Ideal.Quotient.mk (mI A (AdjoinInv B t)) b
    have hx : x * x = x := by
      rw [← sub_eq_zero, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    have hy : y * y = y := by
      rw [← sub_eq_zero, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have h3 : (x - y) ^ 3 = x - y := by
      linear_combination (x + 1 - 3 * y) * hx + (3 * x - y - 1) * hy
    have hodd : ∀ k : ℕ, (x - y) ^ (2 * k + 1) = x - y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ih, ← pow_succ', h3]
    have hzero : (x - y) ^ n = 0 := by
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hn
    have hv : x - y = 0 := by
      rw [← hodd n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hzero, zero_mul]
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact hv
  refine ⟨(eB : K), (eC : K), ⟨eB.2, eC.2, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (mem_mS_iff B (eB * eB - eB)).2 heB
  · exact (mem_mS_iff C (eC * eC - eC)).2 heC
  · exact (mem_mS_iff (AdjoinInv B t) (a - b)).2 hmem
  · rintro ⟨h1, h2⟩
    have hB' : eB ∈ mI A B := (mem_mS_iff B eB).1 h1
    have hC' : eC ∈ mI A C := (mem_mS_iff C eC).1 h2
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    rcases hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact (hWB q).1 hw (inn eB q hB')
    · exact (hWC q).1 hw (inn eC q hC')
  · rintro ⟨h1, h2⟩
    have hB' : eB - 1 ∈ mI A B := (mem_mS_iff B (eB - 1)).1 h1
    have hC' : eC - 1 ∈ mI A C := (mem_mS_iff C (eC - 1)).1 h2
    ext w
    simp only [Set.mem_univ, iff_true]
    rcases hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact (hWB q).2 (notin eB q hB')
    · exact (hWC q).2 (notin eC q hC')

private def resHom (A : Type) [CommRing A] [IsLocalRing A] (S : Type) [CommRing S] [Algebra A S] :
    IsLocalRing.ResidueField A →+* S ⧸ mI A S :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((Ideal.Quotient.mk (mI A S)).comp (algebraMap A S))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))

/- English proof (translation)
Use `⟨pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j) (Spec.map (CommRingCat.ofHom (resHom A S))) ?_, pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hj, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.
-/
private lemma fibre_map {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A S))) :
    ∃ g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A),
      g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j := by
  refine ⟨pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (Spec.map (CommRingCat.ofHom (resHom A S))) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, hj, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

/- English proof (translation)
Establish `h1 : IsClosedImmersion (cpt A)` using `IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective`. Establish `h2 : IsClosedImmersion (pullback.fst p (cpt A))` using `inferInstance`. Conclude with `(pullback.fst p (cpt A)).isClosedEmbedding.injective`.
-/
private lemma fst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    Function.Injective (pullback.fst p (cpt A)).base := by
  have h1 : IsClosedImmersion (cpt A) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have h2 : IsClosedImmersion (pullback.fst p (cpt A)) := inferInstance
  exact (pullback.fst p (cpt A)).isClosedEmbedding.injective

/- English proof (translation)
Conclude with `congrArg (fun h => h.base q) hg`.
-/
private lemma g_apply {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A))
    (hg : g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (q : PrimeSpectrum (S ⧸ mI A S)) :
    (pullback.fst p (cpt A)).base (g.base q) =
      j.base (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q) := by
  exact congrArg (fun h => h.base q) hg

/- English proof (translation)
Establish `h1 : p.base (j.base x) = (cpt A).base ((pullback.snd p (cpt A)).base w)`. Rewrite using `[hx]`. Conclude with `congrArg (fun (h : pullback p (cpt A) ⟶ Spec (CommRingCat.of A)) => h.base w) (pullback.condition (f := p) (g := cpt A))`. Establish `h2 : p.base (j.base x) = PrimeSpectrum.comap (algebraMap A S) x` using `congrArg (fun h => h.base x) hj`. Establish `hm : mI A S ≤ x.asIdeal`.

Establish `h3 : (PrimeSpectrum.comap (algebraMap A S) x).asIdeal = IsLocalRing.maximalIdeal A`. Rewrite using `[← h2, h1]`. Set `y : PrimeSpectrum (IsLocalRing.ResidueField A)` to `(pullback.snd p (cpt A)).base w`. Establish `hbot : y.asIdeal = ⊥` using `by haveI := y.isPrime`. Conclude with `Ideal.eq_bot_of_prime y.asIdeal`.

Use `show Ideal.comap (IsLocalRing.residue A) y.asIdeal = _`. Rewrite using `[hbot, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]`. Use `show Ideal.map _ _ ≤ _`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `le_of_eq h3.symm`.

Take `⟨q, hq⟩` from `exists_q (mI A S) x hm`. Use `⟨q, fst_inj p ?_⟩` and prove the remaining obligations. Rewrite using `[g_apply p j g hg q, hq, hx]`.
-/
private lemma fibre_pt {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A S)))
    (g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A))
    (hg : g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (w : ↑(pullback p (cpt A))) (x : PrimeSpectrum S)
    (hx : j.base x = (pullback.fst p (cpt A)).base w) : ∃ q, g.base q = w := by
  have h1 : p.base (j.base x) = (cpt A).base ((pullback.snd p (cpt A)).base w) := by
    rw [hx]
    exact congrArg (fun (h : pullback p (cpt A) ⟶ Spec (CommRingCat.of A)) => h.base w)
      (pullback.condition (f := p) (g := cpt A))
  have h2 : p.base (j.base x) = PrimeSpectrum.comap (algebraMap A S) x :=
    congrArg (fun h => h.base x) hj
  have hm : mI A S ≤ x.asIdeal := by
    have h3 : (PrimeSpectrum.comap (algebraMap A S) x).asIdeal = IsLocalRing.maximalIdeal A := by
      rw [← h2, h1]
      let y : PrimeSpectrum (IsLocalRing.ResidueField A) := (pullback.snd p (cpt A)).base w
      have hbot : y.asIdeal = ⊥ := by
        haveI := y.isPrime
        exact Ideal.eq_bot_of_prime y.asIdeal
      show Ideal.comap (IsLocalRing.residue A) y.asIdeal = _
      rw [hbot, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    show Ideal.map _ _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq h3.symm
  obtain ⟨q, hq⟩ := exists_q (mI A S) x hm
  refine ⟨q, fst_inj p ?_⟩
  rw [g_apply p j g hg q, hq, hx]

end UpperTheory.Cb.RestrictionHomomorphisms

open UpperTheory.Cb.RestrictionHomomorphisms in
/- English proof (translation)
Introduce `_ A _ _ K _ _ Z p B C t hc hcov W hW`. Take `⟨jU, jV, _, _, hrange, hU, hV, hiff⟩` from `hcov.ex`. Take `⟨gB, hgB⟩` from `fibre_map p jU hU`. Take `⟨gC, hgC⟩` from `fibre_map p jV hV`. Use `pair_of_maps B C t hc (fun q => gB.base q) (fun q => gC.base q) gB.base.hom.continuous gC.base.hom.continuous ?_ ?_ W hW` and prove the remaining obligations.

Introduce `w`. Establish `hw : (pullback.fst p (cpt A)).base w ∈ Set.range jU ∪ Set.range jV`. Rewrite using `[hrange]`. Conclude with `Set.mem_univ _`. Break down `hw with ⟨x, hx⟩ | ⟨y, hy⟩` into its components or cases.

Conclude with `Or.inl (fibre_pt p jU hU gB hgB w x hx)`. Conclude with `Or.inr (fibre_pt p jV hV gC hgC w y hy)`. Introduce `qB qC Q hB hC`. Apply `fst_inj p` to reduce the goal to its premises. Rewrite using `[g_apply p jU gB hgB qB, g_apply p jV gC hgC qC]`.

Conclude with `(hiff _ _).2 ⟨Q, hB, hC⟩`.
-/
theorem UpperTheory.Cb.finite_over_henselian_fibre_idempotents_lift :
    LateralTheory.E.LZProperCut.LZHensFinite → LateralTheory.E.StdChartsProof.FibreIdem := by
  intro _ A _ _ K _ _ Z p B C t hc hcov W hW
  obtain ⟨jU, jV, _, _, hrange, hU, hV, hiff⟩ := hcov.ex
  obtain ⟨gB, hgB⟩ := fibre_map p jU hU
  obtain ⟨gC, hgC⟩ := fibre_map p jV hV
  refine pair_of_maps B C t hc (fun q => gB.base q) (fun q => gC.base q)
    gB.base.hom.continuous gC.base.hom.continuous ?_ ?_ W hW
  · intro w
    have hw : (pullback.fst p (cpt A)).base w ∈ Set.range jU ∪ Set.range jV := by
      rw [hrange]
      exact Set.mem_univ _
    rcases hw with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl (fibre_pt p jU hU gB hgB w x hx)
    · exact Or.inr (fibre_pt p jV hV gC hgC w y hy)
  · intro qB qC Q hB hC
    apply fst_inj p
    rw [g_apply p jU gB hgB qB, g_apply p jV gC hgC qC]
    exact (hiff _ _).2 ⟨Q, hB, hC⟩
