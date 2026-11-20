import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstants
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `k K K' _ _ _ _ c c' e hce n x T φ S S' hx hS h`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.FieldPair.placeEquiv_ringEquiv c c' e hce`. Establish `hmem : ∀ (P : Place c) (b : K'), b ∈ (Φ P).ring ↔ e.symm b ∈ P.ring` using `fun P b => by`. Simplify using `using (hΦ P).1 (e.symm b)`. Establish `hord : ∀ (P : Place c) (b : K'), (Φ P).ord b = P.ord (e.symm b)` using `fun P b => by`.

Simplify using `using (hΦ P).2.1 (e.symm b)`. Establish `hdisc : ∀ P : Place c, (Φ P).disc (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) = P.disc (dForm c x) φ` using `fun P => by`. Simplify using `only [Place.disc]`. Rewrite using `[(hΦ P).2.2.1 φ, (hΦ P).2.2.2 n x hx]`. Establish `hΦS : Φ S = S'` using `Place.ext (ValuationSubring.ext _ _ fun b => by`.

Rewrite using `[hmem, ← hS (e.symm b), e.apply_symm_apply])`. Establish `hk : Klt c n ⊤ (dForm c x) φ` using `⟨h.1, h.2.1, fun P hP => (P.ring_ne_top (eq_top_iff.2 fun f _ => hP f trivial)).elim⟩`. Establish `hk'` using `((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x ⊤ φ hx).2.2.1).1 hk`. Use `⟨hk'.1, hk'.2.1, ?_⟩` and prove the remaining obligations. Introduce `Q' hQ' t' u' E' hTQ hmax hdim hSQ hEQ ht hu hoth`.

Use `set Q : Subring K := Q'.map e.symm.toRingHom with hQdef`. Establish `hQmem : ∀ a : K, a ∈ Q ↔ e a ∈ Q'` using `fun a => by`. Conclude with `Subring.mem_map_equiv (f := e.symm) (K := Q')`. Establish `hQQ : Q.map e.toRingHom = Q'`. Use extensionality with `b`.

Conclude with `(Subring.mem_map_equiv (f := e) (K := Q)).trans ((hQmem _).trans (by rw [e.apply_symm_apply]))`. Establish `hQ : IsLocModel c Q` using `((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x Q φ hx).2.1).2 (hQQ ▸ hQ')`. Set `ψ : Q' ≃+* Q` to `e.symm.subringMap`. Establish `hψ : ∀ y, ((ψ y : Q) : K) = e.symm y` using `fun y => rfl`. Establish `hprime : ∀ P : Place c, (Φ P).IsPrimeOf Q' ↔ P.IsPrimeOf Q`.

Introduce `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun f hf => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Use `h1 (e f) ((hQmem f).1 hf)` as an intermediate fact.

Rewrite `this` using `[hmem, e.symm_apply_apply]`. Then use the resulting hypothesis. Take `⟨a, ha, b, hb, hb0, hbo, hfab⟩` from `h2 (e f) (by rw [hmem, e.symm_apply_apply]; exact hf)`. Use `⟨e.symm a, by rw [hQmem, e.apply_symm_apply]; exact ha, e.symm b, by rw [hQmem, e.apply_symm_apply]; exact hb, by simpa using hb0, by rw [← hord]; exact hbo, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, e.apply_symm_apply, e.apply_symm_apply, hfab]`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun f hf => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hmem]`. Conclude with `h1 _ (by rw [hQmem, e.apply_symm_apply]; exact hf)`. Take `⟨a, ha, b, hb, hb0, hbo, hfab⟩` from `h2 (e.symm f) ((hmem P f).1 hf)`.

Use `⟨e a, (hQmem a).1 ha, e b, (hQmem b).1 hb, by simpa using hb0, by rw [hord, e.symm_apply_apply]; exact hbo, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfab, map_mul, e.apply_symm_apply]`. Use `set E := Φ.symm E' with hEdef`. Establish `hE : Φ E = E'` using `Φ.apply_symm_apply E'`. Use `haveI := hQ'.isLocalRing`.

Use `haveI := hQ.isLocalRing`. Establish `hTQ' : T ≤ Q` using `fun f hf => (hQmem f).2 (hTQ (Subring.mem_map.2 ⟨f, hf, rfl⟩))`. Establish `hmax' : Ideal.span {ψ t', ψ u'} = IsLocalRing.maximalIdeal Q`. Establish `h1` using `congrArg (Ideal.map ψ) hmax`. Rewrite `h1` using `[Ideal.map_span, Set.image_pair]`.

Rewrite using `[h1]`. Use extensionality with `z`. Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite `hy`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Rewrite using `[isUnit_map_iff]` and apply the resulting hypothesis. Introduce `hz`. Use `⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Rewrite using `[isUnit_map_iff ψ.symm]` and apply the resulting hypothesis. Establish `hdim' : ringKrullDim Q = 2`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv ψ]`. Conclude with `hdim`. Establish `hSQ' : S.IsPrimeOf Q` using `(hprime S).1 (hΦS ▸ hSQ)`.

Establish `hEQ' : E.IsPrimeOf Q` using `(hprime E).1 (hE ▸ hEQ)`. Establish `ht' : S.ord ((ψ t' : Q) : K) = 1`. Rewrite using `[hψ, ← hord, hΦS]`. Conclude with `ht`. Establish `hu' : E.ord ((ψ u' : Q) : K) = 1`.

Rewrite using `[hψ, ← hord, hE]`. Conclude with `hu`. Establish `hoth' : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc (dForm c x) φ = 0`. Introduce `P hP hPS hPE`. Rewrite using `[← hdisc]`.

Use `hoth (Φ P) ((hprime P).2 hP) (fun hr => hPS ?_) (fun hr => hPE ?_)` and prove the remaining obligations. Establish `h3 : Φ P = Φ S` using `Place.ext (hr.trans (congrArg Place.ring hΦS).symm)`. Rewrite using `[Φ.injective h3]`. Establish `h3 : Φ P = Φ E` using `Place.ext (hr.trans (congrArg Place.ring hE).symm)`. Rewrite using `[Φ.injective h3]`.

Establish `key` using `h.2.2 Q hQ (ψ t') (ψ u') E hTQ' hmax' hdim' hSQ' hEQ' ht' hu' hoth'`. Rewrite using `[← hE, hdisc]`. Conclude with `key`.
-/
theorem adjKlt_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  intro k K K' _ _ _ _ c c' e hce n x T φ S S' hx hS h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FieldPair.placeEquiv_ringEquiv c c' e hce
  have hmem : ∀ (P : Place c) (b : K'), b ∈ (Φ P).ring ↔ e.symm b ∈ P.ring := fun P b => by
    simpa using (hΦ P).1 (e.symm b)
  have hord : ∀ (P : Place c) (b : K'), (Φ P).ord b = P.ord (e.symm b) := fun P b => by
    simpa using (hΦ P).2.1 (e.symm b)
  have hdisc : ∀ P : Place c, (Φ P).disc (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) =
      P.disc (dForm c x) φ := fun P => by
    simp only [Place.disc]
    rw [(hΦ P).2.2.1 φ, (hΦ P).2.2.2 n x hx]
  have hΦS : Φ S = S' := Place.ext (ValuationSubring.ext _ _ fun b => by
    rw [hmem, ← hS (e.symm b), e.apply_symm_apply])
  have hk : Klt c n ⊤ (dForm c x) φ := ⟨h.1, h.2.1, fun P hP =>
    (P.ring_ne_top (eq_top_iff.2 fun f _ => hP f trivial)).elim⟩
  have hk' := ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x ⊤ φ hx).2.2.1).1 hk
  refine ⟨hk'.1, hk'.2.1, ?_⟩
  intro Q' hQ' t' u' E' hTQ hmax hdim hSQ hEQ ht hu hoth
  set Q : Subring K := Q'.map e.symm.toRingHom with hQdef
  have hQmem : ∀ a : K, a ∈ Q ↔ e a ∈ Q' := fun a => by
    exact Subring.mem_map_equiv (f := e.symm) (K := Q')
  have hQQ : Q.map e.toRingHom = Q' := by
    ext b
    exact (Subring.mem_map_equiv (f := e) (K := Q)).trans ((hQmem _).trans (by rw [e.apply_symm_apply]))
  have hQ : IsLocModel c Q :=
    ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x Q φ hx).2.1).2 (hQQ ▸ hQ')
  let ψ : Q' ≃+* Q := e.symm.subringMap
  have hψ : ∀ y, ((ψ y : Q) : K) = e.symm y := fun y => rfl
  have hprime : ∀ P : Place c, (Φ P).IsPrimeOf Q' ↔ P.IsPrimeOf Q := by
    intro P
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · have := h1 (e f) ((hQmem f).1 hf)
        rwa [hmem, e.symm_apply_apply] at this
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ :=
          h2 (e f) (by rw [hmem, e.symm_apply_apply]; exact hf)
        refine ⟨e.symm a, by rw [hQmem, e.apply_symm_apply]; exact ha,
          e.symm b, by rw [hQmem, e.apply_symm_apply]; exact hb,
          by simpa using hb0, by rw [← hord]; exact hbo, ?_⟩
        apply e.injective
        rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hfab]
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rw [hmem]
        exact h1 _ (by rw [hQmem, e.apply_symm_apply]; exact hf)
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ := h2 (e.symm f) ((hmem P f).1 hf)
        refine ⟨e a, (hQmem a).1 ha, e b, (hQmem b).1 hb, by simpa using hb0,
          by rw [hord, e.symm_apply_apply]; exact hbo, ?_⟩
        rw [← hfab, map_mul, e.apply_symm_apply]
  set E := Φ.symm E' with hEdef
  have hE : Φ E = E' := Φ.apply_symm_apply E'
  haveI := hQ'.isLocalRing
  haveI := hQ.isLocalRing
  have hTQ' : T ≤ Q := fun f hf => (hQmem f).2 (hTQ (Subring.mem_map.2 ⟨f, hf, rfl⟩))
  have hmax' : Ideal.span {ψ t', ψ u'} = IsLocalRing.maximalIdeal Q := by
    have h1 := congrArg (Ideal.map ψ) hmax
    rw [Ideal.map_span, Set.image_pair] at h1
    rw [h1]
    ext z
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      rwa [isUnit_map_iff]
    · intro hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
      rwa [isUnit_map_iff ψ.symm]
  have hdim' : ringKrullDim Q = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ψ]
    exact hdim
  have hSQ' : S.IsPrimeOf Q := (hprime S).1 (hΦS ▸ hSQ)
  have hEQ' : E.IsPrimeOf Q := (hprime E).1 (hE ▸ hEQ)
  have ht' : S.ord ((ψ t' : Q) : K) = 1 := by
    rw [hψ, ← hord, hΦS]
    exact ht
  have hu' : E.ord ((ψ u' : Q) : K) = 1 := by
    rw [hψ, ← hord, hE]
    exact hu
  have hoth' : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.disc (dForm c x) φ = 0 := by
    intro P hP hPS hPE
    rw [← hdisc]
    refine hoth (Φ P) ((hprime P).2 hP) (fun hr => hPS ?_) (fun hr => hPE ?_)
    · have h3 : Φ P = Φ S := Place.ext (hr.trans (congrArg Place.ring hΦS).symm)
      rw [Φ.injective h3]
    · have h3 : Φ P = Φ E := Place.ext (hr.trans (congrArg Place.ring hE).symm)
      rw [Φ.injective h3]
  have key := h.2.2 Q hQ (ψ t') (ψ u') E hTQ' hmax' hdim' hSQ' hEQ' ht' hu' hoth'
  rw [← hE, hdisc]
  exact key

end GlobalTheory.FieldPair
