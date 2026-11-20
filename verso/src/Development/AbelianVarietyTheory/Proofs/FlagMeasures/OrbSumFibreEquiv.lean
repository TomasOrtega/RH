import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsForallHomEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmDataMaximalRealSubfield

namespace GlobalTheory.Mass.RowMean

section Orbits

open GlobalTheory.Mass GlobalTheory.Mass.OrbFib
open scoped ENNReal Classical

variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]

/- English proof (translation)
Establish `h` using `key π hπ x k`. Establish `h0 : ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) ≠ 0`. Establish `: 0 < ENat.card (MulAction.stabilizer G (k • π x))` using `ENat.card_pos`. Conclude with `this.ne'` after adjusting the coercions. Establish `at' : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ ⊤`.

Simplify `hf` using `only [ne_eq, ENat.toENNReal_eq_top]`. Generalize the expression as in `((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) = c at *`. Generalize the expression as in `((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) = b at *`. Generalize the expression as in `(((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) = a at *`. Substitute `h` using the available equality.

Establish `a0 : a ≠ 0` using `left_ne_zero_of_mul h0`. Rewrite using `[ENNReal.mul_inv (Or.inl a0) (Or.inl at'), mul_right_comm, ENNReal.inv_mul_cancel a0 at', one_mul]`.
-/
theorem inv_card_stab (π : α → β) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : α) (k : G)
    (hf : (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard ≠ ⊤) :
    ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ =
      ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) := by
  have h := key π hπ x k
  have h0 : ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) ≠ 0 := by
    have : 0 < ENat.card (MulAction.stabilizer G (k • π x)) := ENat.card_pos
    exact_mod_cast this.ne'
  have at' : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
    simpa only [ne_eq, ENat.toENNReal_eq_top] using hf
  generalize ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) = c at *
  generalize ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) = b at *
  generalize (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) = a at *
  subst h
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  rw [ENNReal.mul_inv (Or.inl a0) (Or.inl at'), mul_right_comm, ENNReal.inv_mul_cancel a0 at', one_mul]

/- English proof (translation)
Establish `e : (n : ℝ≥0∞) * orbSum G Y φ = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) * φ y)`. Unfold `orbSum`. Rewrite using `[← ENNReal.tsum_mul_left]`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[hn _ q.2, ENat.toENNReal_coe, mul_left_comm]`. Rewrite using `[e]`. Unfold `orbSum`. Simplify using `only [encard_orbits X hX, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]`. Rewrite using `[ENNReal.tsum_comm]`.

Use `tsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `q`. Use `set x := Quotient.out q with hx`. Set `r : MulAction.orbitRel.Quotient G β` to `Quotient.mk (MulAction.orbitRel G β) (π x)`. Take `⟨g, hg⟩` from `(mem_orbit_out r (π x)).2 rfl`.

Establish `hr : Quotient.out r = g⁻¹ • π x`. Rewrite using `[← hg]`. Simplify using the standard rewrite rules. Establish `hrY : Quotient.out r ∈ Y` using `hr ▸ hY _ _ (hXY hq)`. Rewrite using `[tsum_eq_single (⟨r, hrY⟩ : {q : MulAction.orbitRel.Quotient G β // Quotient.out q ∈ Y})]`.

Simplify using `only [hr]`. Rewrite using `[hφ, ← mul_assoc, ← inv_card_stab π hπ x g⁻¹]`. Use `ne_top_of_le_ne_top (b := (X ∩ π ⁻¹' {g⁻¹ • π x}).encard) ?_ (Set.encard_le_encard (Set.inter_subset_inter_left _ ?_))` and prove the remaining obligations. Rewrite using `[hn _ (hr ▸ hrY)]`. Conclude with `ENat.coe_ne_top n`.

Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `hX u _ hq`. Introduce `s hs`. Establish `: MulAction.orbit G x ∩ π ⁻¹' {Quotient.out s.1} = ∅`. Use `Set.eq_empty_of_forall_notMem fun z hz => hs (Subtype.ext ?_)` and prove the remaining obligations.

Take `⟨⟨u, rfl⟩, h2⟩` from `hz`. Establish `h3 : π (u • x) = Quotient.out s.1` using `h2`. Use `((mem_orbit_out s.1 (π x)).1 ⟨u⁻¹, ?_⟩).symm` and prove the remaining obligations. Simplify using `[← h3, hπ]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem orbSum_fibre (X : Set α) (Y : Set β) (π : α → β) (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hX : Stable G X) (hY : Stable G Y) (hXY : Set.MapsTo π X Y) (n : ℕ)
    (hn : ∀ y ∈ Y, (X ∩ π ⁻¹' {y}).encard = n) (φ : β → ℝ≥0∞) (hφ : ∀ (g : G) y, φ (g • y) = φ y) :
    orbSum G X (fun x => φ (π x)) = (n : ℝ≥0∞) * orbSum G Y φ := by
  have e : (n : ℝ≥0∞) * orbSum G Y φ =
      orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) * φ y) := by
    unfold orbSum
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun q => ?_
    beta_reduce
    rw [hn _ q.2, ENat.toENNReal_coe, mul_left_comm]
  rw [e]
  unfold orbSum
  simp only [encard_orbits X hX, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun q => ?_
  obtain ⟨q, hq⟩ := q
  set x := Quotient.out q with hx
  let r : MulAction.orbitRel.Quotient G β := Quotient.mk (MulAction.orbitRel G β) (π x)
  obtain ⟨g, hg⟩ := (mem_orbit_out r (π x)).2 rfl
  have hr : Quotient.out r = g⁻¹ • π x := by
    rw [← hg]; simp
  have hrY : Quotient.out r ∈ Y := hr ▸ hY _ _ (hXY hq)
  rw [tsum_eq_single (⟨r, hrY⟩ : {q : MulAction.orbitRel.Quotient G β // Quotient.out q ∈ Y})]
  · simp only [hr]
    rw [hφ, ← mul_assoc, ← inv_card_stab π hπ x g⁻¹]
    refine ne_top_of_le_ne_top (b := (X ∩ π ⁻¹' {g⁻¹ • π x}).encard) ?_
      (Set.encard_le_encard (Set.inter_subset_inter_left _ ?_))
    · rw [hn _ (hr ▸ hrY)]
      exact ENat.coe_ne_top n
    · rintro _ ⟨u, rfl⟩
      exact hX u _ hq
  · intro s hs
    have : MulAction.orbit G x ∩ π ⁻¹' {Quotient.out s.1} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => hs (Subtype.ext ?_)
      obtain ⟨⟨u, rfl⟩, h2⟩ := hz
      have h3 : π (u • x) = Quotient.out s.1 := h2
      refine ((mem_orbit_out s.1 (π x)).1 ⟨u⁻¹, ?_⟩).symm
      simp [← h3, hπ]
    rw [this]; simp

/- English proof (translation)
Use `letI : MulAction G β := MulAction.compHom β e.toMonoidHom`. Establish `hY' : Stable G Y` using `fun g y hy => hY (e g) y hy`. Rewrite using `[orbSum_fibre X Y π hπ hX hY' hXY n hn φ fun g y => hφ (e g) y]`. Use `congr 1`. Conclude with `OrbTransport.main G G' β β e id Y Y φ hY' hY (Set.bijOn_id Y) (fun _ _ _ => rfl) hφ`.
-/
theorem orbSum_fibre_equiv {G G' α β : Type} [Group G] [Group G'] [MulAction G α] [MulAction G' β]
    (e : G ≃* G') (X : Set α) (Y : Set β) (π : α → β) (hπ : ∀ (g : G) x, π (g • x) = e g • π x)
    (hX : Stable G X) (hY : Stable G' Y) (hXY : Set.MapsTo π X Y) (n : ℕ)
    (hn : ∀ y ∈ Y, (X ∩ π ⁻¹' {y}).encard = n) (φ : β → ℝ≥0∞) (hφ : ∀ (g : G') y, φ (g • y) = φ y) :
    orbSum G X (fun x => φ (π x)) = (n : ℝ≥0∞) * orbSum G' Y φ := by
  letI : MulAction G β := MulAction.compHom β e.toMonoidHom
  have hY' : Stable G Y := fun g y hy => hY (e g) y hy
  rw [orbSum_fibre X Y π hπ hX hY' hXY n hn φ fun g y => hφ (e g) y]
  congr 1
  exact OrbTransport.main G G' β β e id Y Y φ hY' hY (Set.bijOn_id Y) (fun _ _ _ => rfl) hφ

end Orbits

section Cyclic

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.SplitOver GlobalTheory.NormOneSplit

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
/- English proof (translation)
Establish `ld` using `locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Take `⟨a1, a2, -, -, a5⟩` from `isomAct (𝓞 K) K V h g hg M`. Establish `b1` using `(ld (gmap g M) (a5.2 hM).fg).1 P hP`. Establish `b2` using `(ld N hN.fg).1 P hP`. Rewrite using `[b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]`.
-/
theorem gmap_loc_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (M N : Submodule (𝓞 K) V)
    (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (g : V ≃ₗ[K] V) (hg : g ∈ isom h) (hgL : gmap g (loc (K := K) P M) = loc (K := K) P N) :
    gmap g (loc (K := K) P (dual h M)) = loc (K := K) P (dual h N) := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
  have b1 := (ld (gmap g M) (a5.2 hM).fg).1 P hP
  have b2 := (ld N hN.fg).1 P hP
  rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]

/- English proof (translation)
Use `haveI := Fact.mk hT`. Use `haveI := finite_hom (E := K) hT`. Use `letI := Fintype.ofFinite (𝓞 K →+* ZMod T)`. Take `⟨hMi, hd⟩` from `(DiscOrder.main K V h hK hs hn L hL).2.2.2.1 M hM`. Use `⟨hMi, ?_⟩` and prove the remaining obligations.

Take `⟨x₀, hx₀, g1, g2⟩` from `(cyc_iff _ _ _).1 e`. Establish `sm : ∀ (g : V ≃ₗ[K] V) (r : 𝓞 K) (v : V), g (r • v) = r • g v` using `fun g r v => (g.toLinearMap.restrictScalars (𝓞 K)).map_smul r v`. Establish `kill : ∀ r ∈ Ideal.span {(T : 𝓞 K)}, ∀ y ∈ dual h M, r • y ∈ M`. Introduce `r hr y hy`. Use `genusBasic_lg (K := K) M _ fun P hP => ?_` and prove the remaining obligations.

Take `⟨g, hg, hgL⟩` from `hM.2 P hP`. Establish `h1 : y ∈ loc (K` using `K) P (dual h M) := locBasic_le_locS _ _ hy`. Rewrite `h1` using `[← gmap_loc_dual h hs L M hL.1 hM.1 P hP.isPrime g hg hgL]`. Take `⟨w, ⟨s, hs', hw⟩, rfl⟩` from `h1`. Rewrite using `[← hgL]`.

Use `⟨r • w, ⟨s, hs', ?_⟩, sm g r w⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `smul_mem_of_gen g1 g2 hr hw`. Establish `ex : ∀ ψ : 𝓞 K →+* ZMod T, ∃ x ∈ dual h M, ∀ r : 𝓞 K, r • x ∈ M → ψ r = 0`. Introduce `ψ`.

Establish `hP` using `ker_isMaximal ψ`. Take `⟨g, hg, hgL⟩` from `hM.2 _ hP`. Establish `h1 : g x₀ ∈ gmap g (loc (K` using `K) (RingHom.ker ψ) (dual h L)) := ⟨x₀, locBasic_le_locS _ _ hx₀, rfl⟩`. Rewrite `h1` using `[gmap_loc_dual h hs L M hL.1 hM.1 _ hP.isPrime g hg hgL]`. Take `⟨s, hs', hw⟩` from `h1`.

Use `⟨_, hw, fun r hr => ?_⟩` and prove the remaining obligations. Establish `h2 : r • s • g x₀ ∈ loc (K` using `K) (RingHom.ker ψ) M := locBasic_le_locS _ _ hr`. Rewrite `h2` using `[← hgL]`. Take `⟨w, ⟨t, ht, hw'⟩, e2⟩` from `h2`. Establish `e3 : w = r • s • x₀` using `g.injective (by rw [sm, sm]; exact e2)`.

Rewrite `hw'` using `[e3, ← mul_smul, ← mul_smul, g2, mem_span_iff hT hsp]`. Establish `h4` using `hw' ψ`. Rewrite `h4` using `[map_mul, map_mul]`. Establish `s0 : ψ s ≠ 0` using `genusBasic_hS (K := K) _ hP s hs'`. Establish `t0 : ψ t ≠ 0` using `genusBasic_hS (K := K) _ hP t ht`.

Simplify `h4` using `[s0, t0]`. Use `choose xs hxs hann using ex`. Use `choose es hes using fun ψ : 𝓞 K →+* ZMod T => exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => if χ = ψ then 1 else 0)`. Establish `hx : ∑ ψ, es ψ • xs ψ ∈ dual h M` using `Submodule.sum_mem _ fun ψ _ => Submodule.smul_mem _ _ (hxs ψ)`. Establish `ann : ∀ r : 𝓞 K, r • ∑ ψ, es ψ • xs ψ ∈ M ↔ r ∈ Ideal.span {(T : 𝓞 K)}`.

Use `fun r => ⟨fun hr => (mem_span_iff hT hsp r).2 fun ψ => ?_, fun hr => kill r hr _ hx⟩` and prove the remaining obligations. Establish `h1` using `M.smul_mem (es ψ) hr`. Rewrite `h1` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ψ), smul_add, smul_add]`. Establish `h2 : es ψ • r • ∑ χ ∈ Finset.univ.erase ψ, es χ • xs χ ∈ M`. Rewrite using `[Finset.smul_sum, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun χ hχ => ?_` and prove the remaining obligations. Rewrite using `[← mul_smul, ← mul_smul]`. Use `kill _ ((mem_span_iff hT hsp _).2 fun ρ => ?_) _ (hxs χ)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hes, hes]`. Distinguish the cases in `h3 : ρ = χ`.

Rewrite using `[if_neg (h3 ▸ Finset.ne_of_mem_erase hχ), zero_mul, zero_mul]`. Rewrite using `[if_neg h3, mul_zero]`. Establish `h3` using `(Submodule.add_mem_iff_left _ h2).1 h1`. Rewrite `h3` using `[← mul_smul, ← mul_smul]`. Establish `h4` using `hann ψ _ h3`.

Simplify `h4` using `[hes]`. Use `⟨_, hx, ?_, ann⟩` and prove the remaining obligations. Use `set x := ∑ ψ, es ψ • xs ψ`. Set `f : 𝓞 K →ₗ[𝓞 K] (↥(dual h M) ⧸ M.comap (dual h M).subtype)` to `(M.comap (dual h M).subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (dual h M) ⟨x, hx⟩`. Establish `hk : Ideal.span {(T : 𝓞 K)} = LinearMap.ker f`.

Use extensionality with `r`. Rewrite using `[← ann, LinearMap.mem_ker]`. Conclude with `(Submodule.Quotient.mk_eq_zero (M.comap (dual h M).subtype) (x := r • (⟨x, hx⟩ : dual h M))).symm`. Set `f'` to `Submodule.liftQ (Ideal.span {(T : 𝓞 K)}) f hk.le`. Establish `inj : Function.Injective f'` using `LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hk.ge)`.

Establish `hc : Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) = Nat.card (↥(dual h M) ⧸ M.comap (dual h M).subtype)`. Take `⟨e⟩` from `e`. Rewrite using `[← Nat.card_congr e.toEquiv]`. Conclude with `hd.symm`. Use `haveI : Finite (↥(dual h M) ⧸ M.comap (dual h M).subtype) := Nat.finite_of_card_ne_zero (DiscOrder.main K V h hK hs hn M hMi).1`.

Establish `sur` using `((Nat.bijective_iff_injective_and_card f').2 ⟨inj, hc⟩).2`. Introduce `y hy`. Take `⟨a, ha⟩` from `sur (Submodule.Quotient.mk ⟨y, hy⟩)`. Take `⟨r, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Conclude with `⟨r, (Submodule.Quotient.eq (M.comap (dual h M).subtype) (x := ⟨y, hy⟩) (y := r • (⟨x, hx⟩ : dual h M))).1 ha.symm⟩`.
-/
theorem cyclic_of_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate)
    {T : ℕ} (hT : T.Prime)
    (hsp : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (e : Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})))
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) :
    IsIntLat h M ∧ ∃ x ∈ dual h M, (∀ y ∈ dual h M, ∃ r : 𝓞 K, y - r • x ∈ M) ∧
      ∀ r : 𝓞 K, r • x ∈ M ↔ r ∈ Ideal.span {(T : 𝓞 K)} := by
  classical
  haveI := Fact.mk hT
  haveI := finite_hom (E := K) hT
  letI := Fintype.ofFinite (𝓞 K →+* ZMod T)
  obtain ⟨hMi, hd⟩ := (DiscOrder.main K V h hK hs hn L hL).2.2.2.1 M hM
  refine ⟨hMi, ?_⟩
  obtain ⟨x₀, hx₀, g1, g2⟩ := (cyc_iff _ _ _).1 e
  have sm : ∀ (g : V ≃ₗ[K] V) (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun g r v =>
    (g.toLinearMap.restrictScalars (𝓞 K)).map_smul r v
  have kill : ∀ r ∈ Ideal.span {(T : 𝓞 K)}, ∀ y ∈ dual h M, r • y ∈ M := by
    intro r hr y hy
    refine genusBasic_lg (K := K) M _ fun P hP => ?_
    obtain ⟨g, hg, hgL⟩ := hM.2 P hP
    have h1 : y ∈ loc (K := K) P (dual h M) := locBasic_le_locS _ _ hy
    rw [← gmap_loc_dual h hs L M hL.1 hM.1 P hP.isPrime g hg hgL] at h1
    obtain ⟨w, ⟨s, hs', hw⟩, rfl⟩ := h1
    rw [← hgL]
    refine ⟨r • w, ⟨s, hs', ?_⟩, sm g r w⟩
    rw [smul_comm]
    exact smul_mem_of_gen g1 g2 hr hw
  have ex : ∀ ψ : 𝓞 K →+* ZMod T, ∃ x ∈ dual h M, ∀ r : 𝓞 K, r • x ∈ M → ψ r = 0 := by
    intro ψ
    have hP := ker_isMaximal ψ
    obtain ⟨g, hg, hgL⟩ := hM.2 _ hP
    have h1 : g x₀ ∈ gmap g (loc (K := K) (RingHom.ker ψ) (dual h L)) :=
      ⟨x₀, locBasic_le_locS _ _ hx₀, rfl⟩
    rw [gmap_loc_dual h hs L M hL.1 hM.1 _ hP.isPrime g hg hgL] at h1
    obtain ⟨s, hs', hw⟩ := h1
    refine ⟨_, hw, fun r hr => ?_⟩
    have h2 : r • s • g x₀ ∈ loc (K := K) (RingHom.ker ψ) M := locBasic_le_locS _ _ hr
    rw [← hgL] at h2
    obtain ⟨w, ⟨t, ht, hw'⟩, e2⟩ := h2
    have e3 : w = r • s • x₀ := g.injective (by rw [sm, sm]; exact e2)
    rw [e3, ← mul_smul, ← mul_smul, g2, mem_span_iff hT hsp] at hw'
    have h4 := hw' ψ
    rw [map_mul, map_mul] at h4
    have s0 : ψ s ≠ 0 := genusBasic_hS (K := K) _ hP s hs'
    have t0 : ψ t ≠ 0 := genusBasic_hS (K := K) _ hP t ht
    simpa [s0, t0] using h4
  choose xs hxs hann using ex
  choose es hes using fun ψ : 𝓞 K →+* ZMod T =>
    exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => if χ = ψ then 1 else 0)
  have hx : ∑ ψ, es ψ • xs ψ ∈ dual h M :=
    Submodule.sum_mem _ fun ψ _ => Submodule.smul_mem _ _ (hxs ψ)
  have ann : ∀ r : 𝓞 K, r • ∑ ψ, es ψ • xs ψ ∈ M ↔ r ∈ Ideal.span {(T : 𝓞 K)} := by
    refine fun r => ⟨fun hr => (mem_span_iff hT hsp r).2 fun ψ => ?_, fun hr => kill r hr _ hx⟩
    have h1 := M.smul_mem (es ψ) hr
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ψ), smul_add, smul_add] at h1
    have h2 : es ψ • r • ∑ χ ∈ Finset.univ.erase ψ, es χ • xs χ ∈ M := by
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Submodule.sum_mem _ fun χ hχ => ?_
      rw [← mul_smul, ← mul_smul]
      refine kill _ ((mem_span_iff hT hsp _).2 fun ρ => ?_) _ (hxs χ)
      rw [map_mul, map_mul, hes, hes]
      by_cases h3 : ρ = χ
      · rw [if_neg (h3 ▸ Finset.ne_of_mem_erase hχ), zero_mul, zero_mul]
      · rw [if_neg h3, mul_zero]
    have h3 := (Submodule.add_mem_iff_left _ h2).1 h1
    rw [← mul_smul, ← mul_smul] at h3
    have h4 := hann ψ _ h3
    simpa [hes] using h4
  refine ⟨_, hx, ?_, ann⟩
  set x := ∑ ψ, es ψ • xs ψ
  let f : 𝓞 K →ₗ[𝓞 K] (↥(dual h M) ⧸ M.comap (dual h M).subtype) :=
    (M.comap (dual h M).subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (dual h M) ⟨x, hx⟩
  have hk : Ideal.span {(T : 𝓞 K)} = LinearMap.ker f := by
    ext r
    rw [← ann, LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (M.comap (dual h M).subtype)
      (x := r • (⟨x, hx⟩ : dual h M))).symm
  let f' := Submodule.liftQ (Ideal.span {(T : 𝓞 K)}) f hk.le
  have inj : Function.Injective f' :=
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hk.ge)
  have hc : Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) =
      Nat.card (↥(dual h M) ⧸ M.comap (dual h M).subtype) := by
    obtain ⟨e⟩ := e
    rw [← Nat.card_congr e.toEquiv]
    exact hd.symm
  haveI : Finite (↥(dual h M) ⧸ M.comap (dual h M).subtype) :=
    Nat.finite_of_card_ne_zero (DiscOrder.main K V h hK hs hn M hMi).1
  have sur := ((Nat.bijective_iff_injective_and_card f').2 ⟨inj, hc⟩).2
  intro y hy
  obtain ⟨a, ha⟩ := sur (Submodule.Quotient.mk ⟨y, hy⟩)
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact ⟨r, (Submodule.Quotient.eq (M.comap (dual h M).subtype) (x := ⟨y, hy⟩)
    (y := r • (⟨x, hx⟩ : dual h M))).1 ha.symm⟩

/- English proof (translation)
Use `haveI := Fact.mk hT`. Use `haveI := finite_hom (E := K) hT`. Establish `hcm` using `GlobalTheory.StdDefinite.cmData_maximalRealSubfield hK`. Establish `hcop : IsCoprime c (T : 𝓞 K)`. Establish `h0 : ∀ ψ : 𝓞 K →+* ZMod T, ψ c ≠ 0`.

Introduce `ψ hψ`. Take `⟨u, hu⟩` from `exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => if χ = ψ then 1 else 0)`. Use `(mem_span_iff hT hsp _).1 (hc' u ((mem_span_iff hT hsp _).2 fun χ => ?_)) ψ` as an intermediate fact. Simplify using `[hu] at this`. Rewrite using `[map_mul, hu]`.

Distinguish the cases in `h1 : χ = ψ`. Rewrite using `[h1, hψ, mul_zero]`. Rewrite using `[if_neg h1, zero_mul]`. Take `⟨u, hu⟩` from `exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => (χ c)⁻¹)`. Establish `: 1 - u * c ∈ Ideal.span {(T : 𝓞 K)}` using `(mem_span_iff hT hsp _).2 fun χ => by`.

Rewrite using `[map_sub, map_mul, hu, inv_mul_cancel₀ (h0 χ), map_one, sub_self]`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨u, v, by rw [hv]; ring⟩`. Establish `sp : ∀ r : 𝓞 K, ((cj r : 𝓞 K) : K) = star (r : K)` using `fun r => locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r`. Establish `key` using `card_norm_classes _ K hcm T hT hsp c (by rw [← sp, hc]) hcop`.

Establish `hf : Module.finrank ℚ (maximalRealSubfield K) = fDeg K` using `by haveI := hK.1`. Establish `h1` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K`. Establish `h2` using `IsTotallyComplex.finrank K`. Establish `h3` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`. Rewrite `h3` using `[IsTotallyComplex.nrRealPlaces_eq_zero]`.

Rewrite `h1` using `[hcm.deg2]`. Unfold `fDeg`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hf, ← key]`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun a => ⟨?_, ?_⟩)` and prove the remaining obligations.

Introduce and unpack `⟨b, h1, h2⟩`. Conclude with `⟨b, cj b, h1, sp b, h2⟩`. Introduce and unpack `⟨b, y, h1, h2, h3⟩`. Use `⟨b, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[show cj b = y from RingOfIntegers.ext ((sp b).trans h2.symm)]` and apply the resulting hypothesis.
-/
theorem card_classes (hK : IsCMUnram K) {T : ℕ} (hT : T.Prime)
    (hsp : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2)
    (c : 𝓞 K) (hc : cj c = c)
    (hc' : ∀ r : 𝓞 K, r * c ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)}) :
    Nat.card {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} // ∃ b : 𝓞 K, Ideal.Quotient.mk _ b = a ∧
      b * cj b - c ∈ Ideal.span {(T : 𝓞 K)}} = (T - 1) ^ fDeg K := by
  classical
  haveI := Fact.mk hT
  haveI := finite_hom (E := K) hT
  have hcm := GlobalTheory.StdDefinite.cmData_maximalRealSubfield hK
  have hcop : IsCoprime c (T : 𝓞 K) := by
    have h0 : ∀ ψ : 𝓞 K →+* ZMod T, ψ c ≠ 0 := by
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => if χ = ψ then 1 else 0)
      have := (mem_span_iff hT hsp _).1 (hc' u ((mem_span_iff hT hsp _).2 fun χ => ?_)) ψ
      · simp [hu] at this
      · rw [map_mul, hu]
        by_cases h1 : χ = ψ
        · rw [h1, hψ, mul_zero]
        · rw [if_neg h1, zero_mul]
    obtain ⟨u, hu⟩ := exists_forall_hom_eq (R := 𝓞 K) (T := T) (fun χ => (χ c)⁻¹)
    have : 1 - u * c ∈ Ideal.span {(T : 𝓞 K)} := (mem_span_iff hT hsp _).2 fun χ => by
      rw [map_sub, map_mul, hu, inv_mul_cancel₀ (h0 χ), map_one, sub_self]
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, v, by rw [hv]; ring⟩
  have sp : ∀ r : 𝓞 K, ((cj r : 𝓞 K) : K) = star (r : K) := fun r =>
    locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r
  have key := card_norm_classes _ K hcm T hT hsp c (by rw [← sp, hc]) hcop
  have hf : Module.finrank ℚ (maximalRealSubfield K) = fDeg K := by
    haveI := hK.1
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
    have h2 := IsTotallyComplex.finrank K
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero] at h3
    rw [hcm.deg2] at h1
    unfold fDeg
    omega
  rw [← hf, ← key]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ⟨?_, ?_⟩)
  · rintro ⟨b, h1, h2⟩
    exact ⟨b, cj b, h1, sp b, h2⟩
  · rintro ⟨b, y, h1, h2, h3⟩
    refine ⟨b, h1, ?_⟩
    rwa [show cj b = y from RingOfIntegers.ext ((sp b).trans h2.symm)]

end Cyclic

section Glue

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.SplitOver

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def glue (U : Submodule K V) (M : Submodule (𝓞 K) U) (x : U) (z : V) (t : K) : Submodule (𝓞 K) V :=
  (M.map (U.subtype.restrictScalars (𝓞 K)) ⊔ Submodule.span (𝓞 K) {(x : V) + t • z}) ⊔
    Submodule.span (𝓞 K) {z}

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
/- English proof (translation)
Establish `e : ∀ (m : U) (r s : 𝓞 K), ((m + r • x : U) : V) + (algebraMap (𝓞 K) K r * t + algebraMap (𝓞 K) K s) • z = (m : V) + r • ((x : V) + t • z) + s • z`. Introduce `m r s`. Rewrite using `[add_smul, mul_smul, algebraMap_smul, algebraMap_smul, smul_add, Submodule.coe_add, Submodule.coe_smul_of_tower]`. Normalize the expressions using the abelian group laws. Simplify using `only [e, glue, Submodule.mem_sup, Submodule.mem_span_singleton, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨_, ⟨m, hm, rfl⟩, _, ⟨r, rfl⟩, rfl⟩, _, ⟨s, rfl⟩, rfl⟩`. Conclude with `⟨m, hm, r, s, rfl⟩`. Introduce and unpack `⟨m, hm, r, s, rfl⟩`. Conclude with `⟨_, ⟨_, ⟨m, hm, rfl⟩, _, ⟨r, rfl⟩, rfl⟩, _, ⟨s, rfl⟩, rfl⟩`.
-/
theorem mem_glue (U : Submodule K V) (M : Submodule (𝓞 K) U) (x : U) (z : V) (t : K) (w : V) :
    w ∈ glue U M x z t ↔ ∃ m ∈ M, ∃ r s : 𝓞 K,
      w = ((m + r • x : U) : V) + (algebraMap (𝓞 K) K r * t + algebraMap (𝓞 K) K s) • z := by
  have e : ∀ (m : U) (r s : 𝓞 K), ((m + r • x : U) : V) +
      (algebraMap (𝓞 K) K r * t + algebraMap (𝓞 K) K s) • z = (m : V) + r • ((x : V) + t • z) + s • z := by
    intro m r s
    rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul, smul_add, Submodule.coe_add,
      Submodule.coe_smul_of_tower]
    abel
  simp only [e, glue, Submodule.mem_sup, Submodule.mem_span_singleton, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨_, ⟨m, hm, rfl⟩, _, ⟨r, rfl⟩, rfl⟩, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, r, s, rfl⟩
  · rintro ⟨m, hm, r, s, rfl⟩
    exact ⟨_, ⟨_, ⟨m, hm, rfl⟩, _, ⟨r, rfl⟩, rfl⟩, _, ⟨s, rfl⟩, rfl⟩

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) {T : ℕ} (hT : T.Prime) {z : V} {U : Submodule K V}
  (hz : h z z = -(T : K)) (hU : ∀ v, v ∈ U ↔ h z v = 0)

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
include hT hz hU in
/- English proof (translation)
Establish `T0 : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT.ne_zero`. Use `⟨⟨v + (h z v / T) • z, (hU _).2 ?_⟩, -(h z v / T), by simp⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, hz, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp (v : V) : ∃ (u : U) (t : K), v = u + t • z := by
  have T0 : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  refine ⟨⟨v + (h z v / T) • z, (hU _).2 ?_⟩, -(h z v / T), by simp⟩
  rw [map_add, map_smul, hz, smul_eq_mul]
  field_simp
  ring

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
include hs hz hU in
/- English proof (translation)
Establish `h1 : ∀ u : U, h z u = 0` using `fun u => (hU _).1 u.2`. Establish `h2 : ∀ u : U, h u z = 0` using `fun u => by rw [← hs.eq, h1, map_zero]`. Establish `h3 : hRes h U u u' = h u u'` using `rfl`. Simplify using `only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, h2, hz, h3, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair (u u' : U) (t t' : K) :
    h (u + t • z) (u' + t' • z) = hRes h U u u' - T * star t * t' := by
  have h1 : ∀ u : U, h z u = 0 := fun u => (hU _).1 u.2
  have h2 : ∀ u : U, h u z = 0 := fun u => by rw [← hs.eq, h1, map_zero]
  have h3 : hRes h U u u' = h u u' := rfl
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, h2, hz, h3,
    smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
  ring

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
include hT hz hU in
/- English proof (translation)
Establish `T0 : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT.ne_zero`. Establish `h1 : ∀ u : U, h z u = 0` using `fun u => (hU _).1 u.2`. Use `congrArg (h z) e` as an intermediate fact. Simplify using `only [map_add, map_smul, h1, hz, smul_eq_mul, zero_add] at this`. Establish `ht : t = t'` using `mul_right_cancel₀ (neg_ne_zero.2 T0) this`.

Rewrite `e` using `[ht]`. Conclude with `⟨Subtype.ext (add_right_cancel e), ht⟩`.
-/
theorem decomp_unique {u u' : U} {t t' : K} (e : (u : V) + t • z = u' + t' • z) : u = u' ∧ t = t' := by
  have T0 : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have h1 : ∀ u : U, h z u = 0 := fun u => (hU _).1 u.2
  have := congrArg (h z) e
  simp only [map_add, map_smul, h1, hz, smul_eq_mul, zero_add] at this
  have ht : t = t' := mul_right_cancel₀ (neg_ne_zero.2 T0) this
  rw [ht] at e
  exact ⟨Subtype.ext (add_right_cancel e), ht⟩

variable {M : Submodule (𝓞 K) U} (hM : IsIntLat (hRes h U) M) {x : U} (hx : x ∈ dual (hRes h U) M)
  (g1 : ∀ y ∈ dual (hRes h U) M, ∃ r : 𝓞 K, y - r • x ∈ M)
  (g2 : ∀ r : 𝓞 K, r • x ∈ M ↔ r ∈ Ideal.span {(T : 𝓞 K)})
  {c : 𝓞 K} (hc : algebraMap (𝓞 K) K c = T * hRes h U x x)
  (hc' : ∀ r : 𝓞 K, r * c ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)})

omit [FiniteDimensional K V] in
include hs hT hz hU hM hx g1 g2 hc hc' in

/- English proof (translation)
Establish `T0 : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT.ne_zero`. Establish `hsU : (hRes h U).IsSymm` using `⟨fun a b => hs.eq (a : V) (b : V)⟩`. Establish `sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r)` using `fun r => (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm`. Take `⟨k, hk⟩` from `Ideal.mem_span_singleton'.1 hb`. Establish `hbu : ∀ r : 𝓞 K, r * b ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)}`.

Introduce `r hr`. Apply `hc'` to reduce the goal to its premises. Establish `: r * c = r * b * cj b - r * (b * cj b - c)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_left _ _ hb)`.

Establish `hbu' : ∀ r : 𝓞 K, r * cj b ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)}`. Introduce `r hr`. Apply `hc'` to reduce the goal to its premises. Establish `: r * c = r * cj b * b - r * (b * cj b - c)` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_left _ _ hb)`. Use `set L := glue U M x z (algebraMap (𝓞 K) K b / T) with hL`. Establish `mem` using `mem_glue U M x z (algebraMap (𝓞 K) K b / T)`. Rewrite `mem` using `[← hL]`. Establish `mM : ∀ m ∈ M, (m : V) ∈ L` using `fun m hm => (mem _).2 ⟨m, hm, 0, 0, by simp⟩`.

Establish `mz : z ∈ L` using `(mem _).2 ⟨0, M.zero_mem, 0, 1, by simp⟩`. Establish `mv : (x : V) + (algebraMap (𝓞 K) K b / T) • z ∈ L` using `(mem _).2 ⟨0, M.zero_mem, 1, 0, by simp⟩`. Establish `hxx : hRes h U x x = algebraMap (𝓞 K) K c / T` using `by rw [hc]; field_simp`. Establish `hkk : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K (cj b) - algebraMap (𝓞 K) K k * T`. Use `congrArg (algebraMap (𝓞 K) K) hk` as an intermediate fact.

Simplify using `only [map_mul, map_sub, map_natCast] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : IsIntegralLat h L`. Introduce `w hw w' hw'`.

Take `⟨m, hm, r, s, rfl⟩` from `(mem w).1 hw`. Take `⟨m', hm', r', s', rfl⟩` from `(mem w').1 hw'`. Take `⟨α, hα⟩` from `Submodule.mem_one.1 (hM.2 m hm m' hm')`. Take `⟨β, hβ⟩` from `Submodule.mem_one.1 ((dualBasic_mem_dual _ M x).1 hx m hm)`. Take `⟨γ, hγ⟩` from `Submodule.mem_one.1 ((dualBasic_mem_dual _ M x).1 hx m' hm')`.

Establish `hγ' : hRes h U x m' = algebraMap (𝓞 K) K (cj γ)`. Rewrite using `[← sp, hγ]`. Conclude with `(hsU.eq _ _).symm`. Rewrite using `[pair h hs hz hU]`. Simplify using `only [map_add, LinearMap.add_apply, genusBasic_hsmul_right, genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]`.

Rewrite using `[← hα, ← hβ, hγ', hxx, hkk]`. Use `Submodule.mem_one.2 ⟨α + r' * β + cj r * cj γ - cj r * r' * k - cj r * cj b * s' - cj s * r' * b - T * cj s * s', ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_sub, map_mul, map_natCast, star_add, star_mul', star_div₀, star_natCast, sp]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨⟨?_, ?_⟩, ?_, fun t => ⟨fun ht => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `((hM.1.fg.map _).sup (Submodule.fg_span_singleton _)).sup (Submodule.fg_span_singleton _)`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨u, t, rfl⟩` from `decomp h hT hz hU v`.

Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span mz))` and prove the remaining obligations. Establish `hu : u ∈ Submodule.span K (M : Set U)` using `by rw [hM.1.span_eq_top]; trivial`. Conclude with `Submodule.span_mono (by rintro _ ⟨m, hm, rfl⟩; exact mM m hm) (Submodule.apply_mem_span_image_of_mem_span U.subtype hu)`. Use `((dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2.2.2 L).2 ⟨hint, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨u, t, rfl⟩` from `decomp h hT hz hU w`.

Establish `hw'` using `(dualBasic_mem_dual h L _).1 hw`. Establish `hu : u ∈ dual (hRes h U) M`. Rewrite using `[dualBasic_mem_dual]`. Introduce `m hm`. Use `pair h hs hz hU m u 0 t` as an intermediate fact.

Simplify using `only [zero_smul, add_zero, star_zero, mul_zero, zero_mul, sub_zero] at this`. Rewrite using `[← this]`. Conclude with `hw' _ (mM m hm)`. Take `⟨r, hr⟩` from `g1 u hu`. Take `⟨s, hs'⟩` from `Submodule.mem_one.1 (hw' z mz)`.

Establish `e1` using `pair h hs hz hU 0 u 1 t`. Simplify using `only [one_smul, Submodule.coe_zero, zero_add, star_one, mul_one, map_zero, LinearMap.zero_apply, zero_sub] at e1`. Rewrite `hs'` using `[e1]`. Establish `w1 : ((u - r • x + r • x : U) : V) + (algebraMap (𝓞 K) K r * (algebraMap (𝓞 K) K b / T) + algebraMap (𝓞 K) K 0) • z ∈ L` using `(mem _).2 ⟨_, hr, r, 0, rfl⟩`. Establish `w2` using `Submodule.sub_mem _ (hw' _ mv) (hint _ mv _ w1)`.

Rewrite `w2` using `[pair h hs hz hU, pair h hs hz hU, sub_add_cancel]`. Take `⟨p, hp⟩` from `Submodule.mem_one.1 w2`. Establish `ht : t = -(algebraMap (𝓞 K) K s) / T` using `by rw [hs']; field_simp`. Establish `: (s + r * b) * cj b ∈ Ideal.span {(T : 𝓞 K)}`. Use `Ideal.mem_span_singleton'.2 ⟨p, genusCovol_hinj (K := K) ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_natCast]`. Rewrite using `[hp, ht]`. Simplify using `only [star_div₀, star_natCast, sp, map_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 (hbu' _ this)`. Use `(mem _).2 ⟨_, hr, r, -q, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_add_cancel]`. Use `congr 2`. Use `congrArg (algebraMap (𝓞 K) K) hq` as an intermediate fact.

Simplify using `only [map_add, map_mul, map_natCast] at this`. Rewrite using `[ht, map_neg]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `this`. Take `⟨m, hm, r, s, e⟩` from `(mem _).1 ht`.

Establish `e' : ((0 : U) : V) + t • z = _` using `(zero_add _).trans e`. Take `⟨e1, rfl⟩` from `decomp_unique h hT hz hU e'`. Establish `: r • x ∈ M`. Rewrite using `[← neg_eq_iff_add_eq_zero.2 e1.symm]`. Conclude with `M.neg_mem hm`.

Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.1 ((g2 r).1 this)`. Use `Submodule.mem_one.2 ⟨q * b + s, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts. Introduce `ht`.

Take `⟨s, rfl⟩` from `Submodule.mem_one.1 ht`. Rewrite using `[algebraMap_smul]`. Conclude with `L.smul_mem s mz`. Use extensionality with `u`. Use `⟨fun hu => ?_, fun hu => mM u hu⟩` and prove the remaining obligations.

Take `⟨m, hm, r, s, e⟩` from `(mem _).1 hu`. Establish `e' : (u : V) + (0 : K) • z = _` using `(by simp : (u : V) + (0 : K) • z = u).trans e`. Take `⟨rfl, e2⟩` from `decomp_unique h hT hz hU e'`. Use `M.add_mem hm ((g2 r).2 (hbu r (Ideal.mem_span_singleton'.2 ⟨-s, genusCovol_hinj (K := K) ?_⟩)))` and prove the remaining obligations. Simplify using `only [map_neg, map_mul, map_natCast]`.

Clear denominators, using `at e2` for the nonvanishing conditions. Take the linear combination `e2`.
-/
theorem glue_spec (b : 𝓞 K) (hb : b * cj b - c ∈ Ideal.span {(T : 𝓞 K)}) :
    Submodule.IsLattice K (glue U M x z (algebraMap (𝓞 K) K b / T)) ∧
    IsUnimodular h (glue U M x z (algebraMap (𝓞 K) K b / T)) ∧
    (∀ t : K, t • z ∈ glue U M x z (algebraMap (𝓞 K) K b / T) ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧
    latIn U (glue U M x z (algebraMap (𝓞 K) K b / T)) = M := by
  have T0 : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hsU : (hRes h U).IsSymm := ⟨fun a b => hs.eq (a : V) (b : V)⟩
  have sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r) := fun r =>
    (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hb
  have hbu : ∀ r : 𝓞 K, r * b ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)} := by
    intro r hr
    apply hc'
    have : r * c = r * b * cj b - r * (b * cj b - c) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_left _ _ hb)
  have hbu' : ∀ r : 𝓞 K, r * cj b ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)} := by
    intro r hr
    apply hc'
    have : r * c = r * cj b * b - r * (b * cj b - c) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_left _ _ hb)
  set L := glue U M x z (algebraMap (𝓞 K) K b / T) with hL
  have mem := mem_glue U M x z (algebraMap (𝓞 K) K b / T)
  rw [← hL] at mem
  have mM : ∀ m ∈ M, (m : V) ∈ L := fun m hm => (mem _).2 ⟨m, hm, 0, 0, by simp⟩
  have mz : z ∈ L := (mem _).2 ⟨0, M.zero_mem, 0, 1, by simp⟩
  have mv : (x : V) + (algebraMap (𝓞 K) K b / T) • z ∈ L := (mem _).2 ⟨0, M.zero_mem, 1, 0, by simp⟩
  have hxx : hRes h U x x = algebraMap (𝓞 K) K c / T := by rw [hc]; field_simp
  have hkk : algebraMap (𝓞 K) K c =
      algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K (cj b) - algebraMap (𝓞 K) K k * T := by
    have := congrArg (algebraMap (𝓞 K) K) hk
    simp only [map_mul, map_sub, map_natCast] at this
    rw [this]; ring
  have hint : IsIntegralLat h L := by
    intro w hw w' hw'
    obtain ⟨m, hm, r, s, rfl⟩ := (mem w).1 hw
    obtain ⟨m', hm', r', s', rfl⟩ := (mem w').1 hw'
    obtain ⟨α, hα⟩ := Submodule.mem_one.1 (hM.2 m hm m' hm')
    obtain ⟨β, hβ⟩ := Submodule.mem_one.1 ((dualBasic_mem_dual _ M x).1 hx m hm)
    obtain ⟨γ, hγ⟩ := Submodule.mem_one.1 ((dualBasic_mem_dual _ M x).1 hx m' hm')
    have hγ' : hRes h U x m' = algebraMap (𝓞 K) K (cj γ) := by
      rw [← sp, hγ]; exact (hsU.eq _ _).symm
    rw [pair h hs hz hU]
    simp only [map_add, LinearMap.add_apply, genusBasic_hsmul_right,
      genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]
    rw [← hα, ← hβ, hγ', hxx, hkk]
    refine Submodule.mem_one.2 ⟨α + r' * β + cj r * cj γ - cj r * r' * k - cj r * cj b * s' -
      cj s * r' * b - T * cj s * s', ?_⟩
    simp only [map_add, map_sub, map_mul, map_natCast, star_add, star_mul', star_div₀, star_natCast, sp]
    field_simp
    ring
  refine ⟨⟨?_, ?_⟩, ?_, fun t => ⟨fun ht => ?_, ?_⟩, ?_⟩
  · exact ((hM.1.fg.map _).sup (Submodule.fg_span_singleton _)).sup (Submodule.fg_span_singleton _)
  · rw [eq_top_iff]
    intro v _
    obtain ⟨u, t, rfl⟩ := decomp h hT hz hU v
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span mz))
    have hu : u ∈ Submodule.span K (M : Set U) := by rw [hM.1.span_eq_top]; trivial
    exact Submodule.span_mono (by rintro _ ⟨m, hm, rfl⟩; exact mM m hm)
      (Submodule.apply_mem_span_image_of_mem_span U.subtype hu)
  · refine ((dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2.2.2 L).2 ⟨hint, fun w hw => ?_⟩
    obtain ⟨u, t, rfl⟩ := decomp h hT hz hU w
    have hw' := (dualBasic_mem_dual h L _).1 hw
    have hu : u ∈ dual (hRes h U) M := by
      rw [dualBasic_mem_dual]
      intro m hm
      have := pair h hs hz hU m u 0 t
      simp only [zero_smul, add_zero, star_zero, mul_zero, zero_mul, sub_zero] at this
      rw [← this]
      exact hw' _ (mM m hm)
    obtain ⟨r, hr⟩ := g1 u hu
    obtain ⟨s, hs'⟩ := Submodule.mem_one.1 (hw' z mz)
    have e1 := pair h hs hz hU 0 u 1 t
    simp only [one_smul, Submodule.coe_zero, zero_add, star_one, mul_one, map_zero, LinearMap.zero_apply,
      zero_sub] at e1
    rw [e1] at hs'
    have w1 : ((u - r • x + r • x : U) : V) + (algebraMap (𝓞 K) K r * (algebraMap (𝓞 K) K b / T) +
      algebraMap (𝓞 K) K 0) • z ∈ L := (mem _).2 ⟨_, hr, r, 0, rfl⟩
    have w2 := Submodule.sub_mem _ (hw' _ mv) (hint _ mv _ w1)
    rw [pair h hs hz hU, pair h hs hz hU, sub_add_cancel] at w2
    obtain ⟨p, hp⟩ := Submodule.mem_one.1 w2
    have ht : t = -(algebraMap (𝓞 K) K s) / T := by rw [hs']; field_simp
    have : (s + r * b) * cj b ∈ Ideal.span {(T : 𝓞 K)} := by
      refine Ideal.mem_span_singleton'.2 ⟨p, genusCovol_hinj (K := K) ?_⟩
      simp only [map_add, map_mul, map_natCast]
      rw [hp, ht]
      simp only [star_div₀, star_natCast, sp, map_zero]
      field_simp
      ring
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hbu' _ this)
    refine (mem _).2 ⟨_, hr, r, -q, ?_⟩
    rw [sub_add_cancel]
    congr 2
    have := congrArg (algebraMap (𝓞 K) K) hq
    simp only [map_add, map_mul, map_natCast] at this
    rw [ht, map_neg]
    field_simp
    linear_combination this
  · obtain ⟨m, hm, r, s, e⟩ := (mem _).1 ht
    have e' : ((0 : U) : V) + t • z = _ := (zero_add _).trans e
    obtain ⟨e1, rfl⟩ := decomp_unique h hT hz hU e'
    have : r • x ∈ M := by
      rw [← neg_eq_iff_add_eq_zero.2 e1.symm]
      exact M.neg_mem hm
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ((g2 r).1 this)
    refine Submodule.mem_one.2 ⟨q * b + s, ?_⟩
    simp only [map_add, map_mul, map_natCast]
    field_simp
  · intro ht
    obtain ⟨s, rfl⟩ := Submodule.mem_one.1 ht
    rw [algebraMap_smul]
    exact L.smul_mem s mz
  · ext u
    refine ⟨fun hu => ?_, fun hu => mM u hu⟩
    obtain ⟨m, hm, r, s, e⟩ := (mem _).1 hu
    have e' : (u : V) + (0 : K) • z = _ := (by simp : (u : V) + (0 : K) • z = u).trans e
    obtain ⟨rfl, e2⟩ := decomp_unique h hT hz hU e'
    refine M.add_mem hm ((g2 r).2 (hbu r (Ideal.mem_span_singleton'.2 ⟨-s, genusCovol_hinj (K := K) ?_⟩)))
    simp only [map_neg, map_mul, map_natCast]
    field_simp at e2
    linear_combination e2

include hs hT hz hU hM hx g1 g2 hc hc' in

/- English proof (translation)
Establish `T0 : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT.ne_zero`. Establish `hsU : (hRes h U).IsSymm` using `⟨fun a b => hs.eq (a : V) (b : V)⟩`. Establish `sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r)` using `fun r => (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm`. Take `⟨an, -, -, -, huni⟩` from `dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Establish `hLu' : dual h L = L` using `hLu`.

Establish `hint` using `((huni L).1 hLu).1`. Establish `mz : z ∈ L` using `by simpa using (hLz 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)`. Set `pr : V →ₗ[K] U` to `LinearMap.codRestrict U (LinearMap.id + ((T : K)⁻¹ • h z).smulRight z) fun v => (hU _).2 (by`. Simplify using `only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, map_add, map_smul, hz, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Establish `hpr : ∀ v, v = (pr v : V) + (-((T : K)⁻¹ * h z v)) • z` using `fun v => by simp [pr]`. Establish `hsur : Function.Surjective pr` using `fun u => ⟨u, by`. Establish `e : (u : V) + (0 : K) • z = _` using `(by simp : (u : V) + (0 : K) • z = u).trans (hpr u)`. Conclude with `(decomp_unique h hT hz hU e).1.symm⟩`.

Set `N : Submodule (𝓞 K) U` to `L.map (pr.restrictScalars (𝓞 K))`. Establish `hN : Submodule.IsLattice K N`. Use `⟨hL.fg.map _, ?_⟩` and prove the remaining obligations. Establish `h1 : (N : Set U) = pr '' (L : Set V)` using `rfl`. Rewrite using `[h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hsur]`.

Establish `hp : ∀ (l : V) (y : U), h l y = hRes h U (pr l) y` using `fun l y => by`. Use `pair h hs hz hU (pr l) y (-((T : K)⁻¹ * h z l)) 0` as an intermediate fact. Rewrite `this` using `[← hpr]`. Simplify using `using this`. Establish `hd : dual (hRes h U) N = M`.

Use extensionality with `y`. Rewrite using `[← hLM, dualBasic_mem_dual]`. Express the relevant statement in the definitionally equal form `_ ↔ (y : V) ∈ L`. Rewrite using `[← hLu', dualBasic_mem_dual]`. Prove the components needed by the constructor for the conclusion.

Introduce `H l hl`. Rewrite using `[hp]`. Conclude with `H _ ⟨l, hl, rfl⟩`. Introduce and unpack `H _ ⟨l, hl, rfl⟩`. Conclude with `hp l y ▸ H l hl`.

Establish `hxN : x ∈ N`. Rewrite using `[← (dualLattice (𝓞 K) K U _ hsU hn star_algebraMap_ringOfIntegers_mem_range N hN).2.1, hd]`. Conclude with `hx`. Take `⟨l, hl, e⟩` from `hxN`. Establish `e' : pr l = x` using `e`.

Take `⟨a, ha⟩` from `Submodule.mem_one.1 (hint z mz l hl)`. Establish `hl' : l = (x : V) + (algebraMap (𝓞 K) K (-a) / T) • z`. Use `(hpr l).trans ?_` and prove the remaining obligations. Rewrite using `[e', ← ha, map_neg]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb : -a * cj (-a) - c ∈ Ideal.span {(T : 𝓞 K)}`. Take `⟨p, hp⟩` from `Submodule.mem_one.1 (hint l hl l hl)`. Rewrite `hp` using `[hl', pair h hs hz hU]`. Use `Ideal.mem_span_singleton'.2 ⟨-p, genusCovol_hinj (K := K) ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sub, map_mul, map_natCast]`. Rewrite using `[map_neg, hp, hc]`. Simplify using `only [star_div₀, star_natCast, sp]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨-a, hb, ?_⟩` and prove the remaining obligations. Establish `hle : glue U M x z (algebraMap (𝓞 K) K (-a) / T) ≤ L`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite `hm` using `[← hLM]`.

Conclude with `hm`. Rewrite using `[Submodule.span_singleton_le_iff_mem, ← hl']`. Conclude with `hl`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `mz`.

Establish `hu : dual h _ = _` using `(glue_spec h hs hT hz hU hM hx g1 g2 hc hc' (-a) hb).2.1`. Use `le_antisymm hle ?_` and prove the remaining obligations. Rewrite using `[← hLu', ← hu]`. Conclude with `an _ _ hle`.
-/
theorem exists_eq_glue (hn : (hRes h U).Nondegenerate) (L : Submodule (𝓞 K) V)
    (hL : Submodule.IsLattice K L) (hLu : IsUnimodular h L)
    (hLz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) (hLM : latIn U L = M) :
    ∃ b : 𝓞 K, b * cj b - c ∈ Ideal.span {(T : 𝓞 K)} ∧ glue U M x z (algebraMap (𝓞 K) K b / T) = L := by
  have T0 : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hsU : (hRes h U).IsSymm := ⟨fun a b => hs.eq (a : V) (b : V)⟩
  have sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r) := fun r =>
    (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm
  obtain ⟨an, -, -, -, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hLu' : dual h L = L := hLu
  have hint := ((huni L).1 hLu).1
  have mz : z ∈ L := by simpa using (hLz 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  let pr : V →ₗ[K] U := LinearMap.codRestrict U
    (LinearMap.id + ((T : K)⁻¹ • h z).smulRight z) fun v => (hU _).2 (by
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.smul_apply, map_add, map_smul, hz, smul_eq_mul]
      field_simp
      ring)
  have hpr : ∀ v, v = (pr v : V) + (-((T : K)⁻¹ * h z v)) • z := fun v => by simp [pr]
  have hsur : Function.Surjective pr := fun u => ⟨u, by
    have e : (u : V) + (0 : K) • z = _ := (by simp : (u : V) + (0 : K) • z = u).trans (hpr u)
    exact (decomp_unique h hT hz hU e).1.symm⟩
  let N : Submodule (𝓞 K) U := L.map (pr.restrictScalars (𝓞 K))
  have hN : Submodule.IsLattice K N := by
    refine ⟨hL.fg.map _, ?_⟩
    have h1 : (N : Set U) = pr '' (L : Set V) := rfl
    rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hsur]
  have hp : ∀ (l : V) (y : U), h l y = hRes h U (pr l) y := fun l y => by
    have := pair h hs hz hU (pr l) y (-((T : K)⁻¹ * h z l)) 0
    rw [← hpr] at this
    simpa using this
  have hd : dual (hRes h U) N = M := by
    ext y
    rw [← hLM, dualBasic_mem_dual]
    change _ ↔ (y : V) ∈ L
    rw [← hLu', dualBasic_mem_dual]
    constructor
    · intro H l hl
      rw [hp]
      exact H _ ⟨l, hl, rfl⟩
    · rintro H _ ⟨l, hl, rfl⟩
      exact hp l y ▸ H l hl
  have hxN : x ∈ N := by
    rw [← (dualLattice (𝓞 K) K U _ hsU hn star_algebraMap_ringOfIntegers_mem_range N hN).2.1, hd]
    exact hx
  obtain ⟨l, hl, e⟩ := hxN
  have e' : pr l = x := e
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hint z mz l hl)
  have hl' : l = (x : V) + (algebraMap (𝓞 K) K (-a) / T) • z := by
    refine (hpr l).trans ?_
    rw [e', ← ha, map_neg]
    congr 2
    ring
  have hb : -a * cj (-a) - c ∈ Ideal.span {(T : 𝓞 K)} := by
    obtain ⟨p, hp⟩ := Submodule.mem_one.1 (hint l hl l hl)
    rw [hl', pair h hs hz hU] at hp
    refine Ideal.mem_span_singleton'.2 ⟨-p, genusCovol_hinj (K := K) ?_⟩
    simp only [map_sub, map_mul, map_natCast]
    rw [map_neg, hp, hc]
    simp only [star_div₀, star_natCast, sp]
    field_simp
    ring
  refine ⟨-a, hb, ?_⟩
  have hle : glue U M x z (algebraMap (𝓞 K) K (-a) / T) ≤ L := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨m, hm, rfl⟩
      rw [← hLM] at hm
      exact hm
    · rw [Submodule.span_singleton_le_iff_mem, ← hl']
      exact hl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact mz
  have hu : dual h _ = _ := (glue_spec h hs hT hz hU hM hx g1 g2 hc hc' (-a) hb).2.1
  refine le_antisymm hle ?_
  rw [← hLu', ← hu]
  exact an _ _ hle

include hs hT hz hU hM hx g1 g2 in

/- English proof (translation)
Establish `T0 : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT.ne_zero`. Establish `hsU : (hRes h U).IsSymm` using `⟨fun a b => hs.eq (a : V) (b : V)⟩`. Establish `sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r)` using `fun r => (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm`. Establish `hx'` using `(dualBasic_mem_dual _ M x).1 hx`. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (hx' _ ((g2 _).2 (Ideal.mem_span_singleton_self _)))`.

Rewrite `hc` using `[genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, map_natCast, map_natCast]`. Establish `hcc : cj c = c` using `genusCovol_hinj (K := K) (by`. Rewrite using `[← sp, hc, star_mul', star_natCast]`. Use `congr 1`. Conclude with `hsU.eq x x)`.

Establish `hc' : ∀ r : 𝓞 K, r * c ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)}`. Introduce `r hr`. Take `⟨k, hk⟩` from `Ideal.mem_span_singleton'.1 hr`. Establish `hk'` using `congrArg (algebraMap (𝓞 K) K) hk`. Rewrite `hk'` using `[map_mul, map_mul, map_natCast, hc]`.

Establish `e : algebraMap (𝓞 K) K r * hRes h U x x = algebraMap (𝓞 K) K k` using `mul_left_cancel₀ T0 (by linear_combination -hk')`. Rewrite using `[← g2, ← (dualLattice (𝓞 K) K U _ hsU hn star_algebraMap_ringOfIntegers_mem_range M hM.1).2.1, dualBasic_mem_dual]`. Introduce `y hy`. Take `⟨a, ha⟩` from `g1 y hy`. Rewrite using `[← sub_add_cancel y (a • x), map_add, LinearMap.add_apply]`.

Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[genusBasic_hsmul_right]`. Conclude with `genusBasic_mem_one_mul _ (hx' _ ha) _`. Rewrite using `[genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right, e]`. Conclude with `genusBasic_mem_one_mul _ (Submodule.mem_one.2 ⟨k, rfl⟩) _`.

Establish `key` using `card_classes hK hT hsp c hcc hc'`. Establish `hb : ∀ a : {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} // ∃ b : 𝓞 K, Ideal.Quotient.mk _ b = a ∧ b * cj b - c ∈ Ideal.span {(T : 𝓞 K)}}, ∃ b : 𝓞 K, Ideal.Quotient.mk _ b = a.1 ∧ b * cj b - c ∈ Ideal.span {(T : 𝓞 K)}` using `fun a => a.2`. Use `choose β hβ1 hβ2 using hb`. Establish `eqv : ∀ b b' : 𝓞 K, b * cj b - c ∈ Ideal.span {(T : 𝓞 K)} → (glue U M x z (algebraMap (𝓞 K) K b' / T) ≤ glue U M x z (algebraMap (𝓞 K) K b / T) ↔ b' - b ∈ Ideal.span {(T : 𝓞 K)})`. Introduce `b b' hb`.

Establish `mv : ∀ t : K, (x : V) + t • z ∈ glue U M x z t` using `fun t => (mem_glue U M x z t _).2 ⟨0, M.zero_mem, 1, 0, by simp⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hle`. Use `Submodule.sub_mem _ (hle (mv _)) (mv _)` as an intermediate fact. Rewrite `this` using `[add_sub_add_left_eq_sub, ← sub_smul, (glue_spec h hs hT hz hU hM hx g1 g2 hc hc' b hb).2.2.1]`.

Take `⟨p, hp⟩` from `Submodule.mem_one.1 this`. Use `Ideal.mem_span_singleton'.2 ⟨p, genusCovol_hinj (K := K) ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hp, map_sub, map_natCast]`. Clear the denominators using the available nonvanishing facts. Introduce `hq w hw`.

Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 hq`. Take `⟨m, hm, r, s, rfl⟩` from `(mem_glue U M x z _ _).1 hw`. Use `(mem_glue U M x z _ _).2 ⟨m, hm, r, s + r * q, ?_⟩` and prove the remaining obligations. Use `congr 2`. Use `congrArg (algebraMap (𝓞 K) K) hq` as an intermediate fact.

Simplify using `only [map_sub, map_mul, map_natCast] at this`. Simplify using `only [map_add, map_mul]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-algebraMap (𝓞 K) K r) * this`. Use `haveI : Finite (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by`.

Simplify `hT.ne_zero)` using `[Ideal.span_singleton_eq_bot]`. Rewrite using `[← key, ← ENat.card_eq_coe_natCard]`. Use `(ENat.card_congr (Equiv.ofBijective (fun a => ⟨glue U M x z (algebraMap (𝓞 K) K (β a) / T), glue_spec h hs hT hz hU hM hx g1 g2 hc hc' _ (hβ2 a)⟩) ⟨fun a a' e => ?_, ?_⟩)).symm` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hβ1 a, ← hβ1 a', Ideal.Quotient.eq]`.

Conclude with `(eqv _ _ (hβ2 a')).1 (congrArg Subtype.val e).le`. Introduce and unpack `⟨L, h1, h2, h3, h4⟩`. Take `⟨b, hb, rfl⟩` from `exists_eq_glue h hs hT hz hU hM hx g1 g2 hc hc' hn L h1 h2 h3 h4`. Use `⟨⟨Ideal.Quotient.mk _ b, b, rfl, hb⟩, Subtype.ext (le_antisymm ?_ ?_)⟩` and prove the remaining obligations. Conclude with `(eqv _ _ hb).2 (Ideal.Quotient.eq.1 (hβ1 _))`.

Conclude with `(eqv _ _ (hβ2 _)).2 (Ideal.Quotient.eq.1 (hβ1 ⟨_, b, rfl, hb⟩).symm)`.
-/
theorem fibre_card (hK : IsCMUnram K) (hn : (hRes h U).Nondegenerate)
    (hsp : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) :
    {L : Submodule (𝓞 K) V | Submodule.IsLattice K L ∧ IsUnimodular h L ∧
      (∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ latIn U L = M}.encard =
      (((T - 1) ^ fDeg K : ℕ) : ℕ∞) := by
  have T0 : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hsU : (hRes h U).IsSymm := ⟨fun a b => hs.eq (a : V) (b : V)⟩
  have sp : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K (cj r) := fun r =>
    (locBasic_sigma_spec genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r).symm
  have hx' := (dualBasic_mem_dual _ M x).1 hx
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx' _ ((g2 _).2 (Ideal.mem_span_singleton_self _)))
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, map_natCast, map_natCast] at hc
  have hcc : cj c = c := genusCovol_hinj (K := K) (by
    rw [← sp, hc, star_mul', star_natCast]
    congr 1
    exact hsU.eq x x)
  have hc' : ∀ r : 𝓞 K, r * c ∈ Ideal.span {(T : 𝓞 K)} → r ∈ Ideal.span {(T : 𝓞 K)} := by
    intro r hr
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hr
    have hk' := congrArg (algebraMap (𝓞 K) K) hk
    rw [map_mul, map_mul, map_natCast, hc] at hk'
    have e : algebraMap (𝓞 K) K r * hRes h U x x = algebraMap (𝓞 K) K k :=
      mul_left_cancel₀ T0 (by linear_combination -hk')
    rw [← g2, ← (dualLattice (𝓞 K) K U _ hsU hn star_algebraMap_ringOfIntegers_mem_range M hM.1).2.1, dualBasic_mem_dual]
    intro y hy
    obtain ⟨a, ha⟩ := g1 y hy
    rw [← sub_add_cancel y (a • x), map_add, LinearMap.add_apply]
    refine Submodule.add_mem _ ?_ ?_
    · rw [genusBasic_hsmul_right]
      exact genusBasic_mem_one_mul _ (hx' _ ha) _
    · rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right, e]
      exact genusBasic_mem_one_mul _ (Submodule.mem_one.2 ⟨k, rfl⟩) _
  have key := card_classes hK hT hsp c hcc hc'
  have hb : ∀ a : {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} // ∃ b : 𝓞 K, Ideal.Quotient.mk _ b = a ∧
      b * cj b - c ∈ Ideal.span {(T : 𝓞 K)}}, ∃ b : 𝓞 K, Ideal.Quotient.mk _ b = a.1 ∧
      b * cj b - c ∈ Ideal.span {(T : 𝓞 K)} := fun a => a.2
  choose β hβ1 hβ2 using hb
  have eqv : ∀ b b' : 𝓞 K, b * cj b - c ∈ Ideal.span {(T : 𝓞 K)} →
      (glue U M x z (algebraMap (𝓞 K) K b' / T) ≤ glue U M x z (algebraMap (𝓞 K) K b / T) ↔
        b' - b ∈ Ideal.span {(T : 𝓞 K)}) := by
    intro b b' hb
    have mv : ∀ t : K, (x : V) + t • z ∈ glue U M x z t := fun t =>
      (mem_glue U M x z t _).2 ⟨0, M.zero_mem, 1, 0, by simp⟩
    constructor
    · intro hle
      have := Submodule.sub_mem _ (hle (mv _)) (mv _)
      rw [add_sub_add_left_eq_sub, ← sub_smul,
        (glue_spec h hs hT hz hU hM hx g1 g2 hc hc' b hb).2.2.1] at this
      obtain ⟨p, hp⟩ := Submodule.mem_one.1 this
      refine Ideal.mem_span_singleton'.2 ⟨p, genusCovol_hinj (K := K) ?_⟩
      rw [map_mul, hp, map_sub, map_natCast]
      field_simp
    · intro hq w hw
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hq
      obtain ⟨m, hm, r, s, rfl⟩ := (mem_glue U M x z _ _).1 hw
      refine (mem_glue U M x z _ _).2 ⟨m, hm, r, s + r * q, ?_⟩
      congr 2
      have := congrArg (algebraMap (𝓞 K) K) hq
      simp only [map_sub, map_mul, map_natCast] at this
      simp only [map_add, map_mul]
      field_simp
      linear_combination (-algebraMap (𝓞 K) K r) * this
  haveI : Finite (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simpa [Ideal.span_singleton_eq_bot] using hT.ne_zero)
  rw [← key, ← ENat.card_eq_coe_natCard]
  refine (ENat.card_congr (Equiv.ofBijective (fun a => ⟨glue U M x z (algebraMap (𝓞 K) K (β a) / T),
    glue_spec h hs hT hz hU hM hx g1 g2 hc hc' _ (hβ2 a)⟩) ⟨fun a a' e => ?_, ?_⟩)).symm
  · apply Subtype.ext
    rw [← hβ1 a, ← hβ1 a', Ideal.Quotient.eq]
    exact (eqv _ _ (hβ2 a')).1 (congrArg Subtype.val e).le
  · rintro ⟨L, h1, h2, h3, h4⟩
    obtain ⟨b, hb, rfl⟩ := exists_eq_glue h hs hT hz hU hM hx g1 g2 hc hc' hn L h1 h2 h3 h4
    refine ⟨⟨Ideal.Quotient.mk _ b, b, rfl, hb⟩, Subtype.ext (le_antisymm ?_ ?_)⟩
    · exact (eqv _ _ hb).2 (Ideal.Quotient.eq.1 (hβ1 _))
    · exact (eqv _ _ (hβ2 _)).2 (Ideal.Quotient.eq.1 (hβ1 ⟨_, b, rfl, hb⟩).symm)

end Glue

section Stabiliser

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.StabSplit

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) {T : ℕ} (hT : T.Prime) {z : V} {U : Submodule K V}
  (hz : h z z = -(T : K)) (hU : ∀ v, v ∈ U ↔ h z v = 0)

omit [NumberField K] in
include hU in
/- English proof (translation)
Establish `hg : g.1.1 z = z` using `g.2`. Establish `hi : ∀ x y, h (g.1.1 x) (g.1.1 y) = h x y` using `g.1.2`. Rewrite using `[smul_eq_map]`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, rfl⟩`. Use `(hi z w).trans ((hU w).1 hw)` as an intermediate fact. Rewrite `this` using `[hg]`. Conclude with `(hU _).2 this`. Introduce `hv`.

Use `⟨g.1.1.symm v, (hU _).2 ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← hi, hg, LinearEquiv.apply_symm_apply]`. Conclude with `(hU v).1 hv`.
-/
theorem smul_compl (g : MulAction.stabilizer (isom h) z) : g.1 • U = U := by
  have hg : g.1.1 z = z := g.2
  have hi : ∀ x y, h (g.1.1 x) (g.1.1 y) = h x y := g.1.2
  rw [smul_eq_map]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have := (hi z w).trans ((hU w).1 hw)
    rw [hg] at this
    exact (hU _).2 this
  · intro hv
    refine ⟨g.1.1.symm v, (hU _).2 ?_, by simp⟩
    rw [← hi, hg, LinearEquiv.apply_symm_apply]
    exact (hU v).1 hv

noncomputable def resZ : MulAction.stabilizer (isom h) z →* isom (hRes h U) :=
  MonoidHom.mk' (fun γ => res h U γ.1 (smul_compl h hU γ)) fun _ _ => rfl

include hs hT hz in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `γ δ e`. Use `Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))` and prove the remaining obligations. Take `⟨u, t, rfl⟩` from `decomp h hT hz hU x`. Establish `k1 : γ.1.1 u = δ.1.1 u` using `congrArg (fun t : isom (hRes h U) => ((t.1 u : U) : V)) e`.

Establish `k2 : γ.1.1 z = z` using `γ.2`. Establish `k3 : δ.1.1 z = z` using `δ.2`. Rewrite using `[map_add, map_add, map_smul, map_smul, k1, k2, k3]`. Introduce `a`. Establish `hc : IsCompl U (Submodule.span K {z})`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `v hv hv'`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hv'`. Establish `e : ((⟨t • z, hv⟩ : U) : V) + (0 : K) • z = (0 : U) + t • z` using `by simp`.

Rewrite using `[← (decomp_unique h hT hz hU e).2, zero_smul]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Take `⟨u, t, rfl⟩` from `decomp h hT hz hU v`. Conclude with `Submodule.add_mem_sup u.2 (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))`.

Set `e` to `Submodule.prodEquivOfIsCompl U _ hc`. Set `g : V ≃ₗ[K] V` to `e.symm ≪≫ₗ (a.1.prodCongr (LinearEquiv.refl K _)) ≪≫ₗ e`. Establish `hg : ∀ (u : U) (t : K), g (u + t • z) = a.1 u + t • z`. Introduce `u t`. Establish `: e.symm (u + t • z) = (u, ⟨t • z, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)⟩)`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [g, LinearEquiv.trans_apply, this]`. Both sides reduce to the same expression. Establish `hi : g ∈ isom h`.

Introduce `x y`. Take `⟨u, t, rfl⟩` from `decomp h hT hz hU x`. Take `⟨u', t', rfl⟩` from `decomp h hT hz hU y`. Rewrite using `[hg, hg, pair h hs hz hU, pair h hs hz hU, a.2]`. Establish `hgz : g z = z` using `by simpa using hg 0 1`.

Use `⟨⟨⟨g, hi⟩, hgz⟩, Subtype.ext (LinearEquiv.ext fun x => Subtype.ext ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g x = _`. Simplify using `using hg x 0`.
-/
theorem resZ_bijective : Function.Bijective (resZ h hU) := by
  constructor
  · intro γ δ e
    refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
    obtain ⟨u, t, rfl⟩ := decomp h hT hz hU x
    have k1 : γ.1.1 u = δ.1.1 u := congrArg (fun t : isom (hRes h U) => ((t.1 u : U) : V)) e
    have k2 : γ.1.1 z = z := γ.2
    have k3 : δ.1.1 z = z := δ.2
    rw [map_add, map_add, map_smul, map_smul, k1, k2, k3]
  · intro a
    have hc : IsCompl U (Submodule.span K {z}) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro v hv hv'
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv'
        have e : ((⟨t • z, hv⟩ : U) : V) + (0 : K) • z = (0 : U) + t • z := by simp
        rw [← (decomp_unique h hT hz hU e).2, zero_smul]
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        obtain ⟨u, t, rfl⟩ := decomp h hT hz hU v
        exact Submodule.add_mem_sup u.2 (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
    let e := Submodule.prodEquivOfIsCompl U _ hc
    let g : V ≃ₗ[K] V := e.symm ≪≫ₗ (a.1.prodCongr (LinearEquiv.refl K _)) ≪≫ₗ e
    have hg : ∀ (u : U) (t : K), g (u + t • z) = a.1 u + t • z := by
      intro u t
      have : e.symm (u + t • z) =
          (u, ⟨t • z, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)⟩) := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [g, LinearEquiv.trans_apply, this]
      rfl
    have hi : g ∈ isom h := by
      intro x y
      obtain ⟨u, t, rfl⟩ := decomp h hT hz hU x
      obtain ⟨u', t', rfl⟩ := decomp h hT hz hU y
      rw [hg, hg, pair h hs hz hU, pair h hs hz hU, a.2]
    have hgz : g z = z := by simpa using hg 0 1
    refine ⟨⟨⟨g, hi⟩, hgz⟩, Subtype.ext (LinearEquiv.ext fun x => Subtype.ext ?_)⟩
    change g x = _
    simpa using hg x 0

end Stabiliser

section Main

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hK hs T z U hT hsp hz hU' hp L₀ hL₀ e φ hφ`. Establish `hU : ∀ v, v ∈ U ↔ h z v = 0`. Introduce `v`. Rewrite using `[hU', StabSplit.mem_perp]`. Use `⟨fun H => H z (Submodule.mem_span_singleton_self z), fun H x hx => ?_⟩` and prove the remaining obligations.

Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, H, smul_zero]`. Establish `hsU : (hRes h U).IsSymm` using `⟨fun a b => hs.eq (a : V) (b : V)⟩`. Establish `hn : (hRes h U).Nondegenerate`. Take `⟨τ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`.

Apply the tactic sequence `constructor <;>`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Use `hp τ x h0` as an intermediate fact. Rewrite `this` using `[hx x]`.

Simplify using `at this`. Establish `hπ : ∀ (g : MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) z) (L : Submodule (𝓞 K) V), latIn U (g • L) = MulEquiv.ofBijective _ (resZ_bijective h hs hT hz hU) g • latIn U L` using `fun g L => StabSplit.latIn_smul h U g.1 (smul_compl h hU g) L`. Establish `hY` using `Transp.genus_stable (h := hRes h U) L₀`. Rewrite using `[← Nat.cast_pow]`. Use `orbSum_fibre_equiv (MulEquiv.ofBijective _ (resZ_bijective h hs hT hz hU)) _ _ (latIn U) hπ ?_ hY (fun L hL => hL.2.2.2) _ (fun M hM => ?_) φ hφ` and prove the remaining obligations.

Introduce and unpack `g L ⟨h1, h2, h3, h4⟩`. Establish `H` using `Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g.1.1 g.1.2 L`. Use `⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, hπ g L ▸ hY _ _ h4⟩` and prove the remaining obligations. Establish `hg : g.1.1 z = z` using `g.2`. Rewrite using `[← h3]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, e'⟩`. Establish `: w = t • z` using `g.1.1.injective (by rw [map_smul, hg]; exact e')`. Conclude with `this ▸ hw`. Introduce `hw`.

Conclude with `⟨t • z, hw, by change g.1.1 (t • z) = _; rw [map_smul, hg]⟩`. Take `⟨hMi, x, hx, g1, g2⟩` from `cyclic_of_genus _ hK hsU hn hT hsp L₀ hL₀ e M hM`. Rewrite using `[← fibre_card h hs hT hz hU hMi hx g1 g2 hK hn hsp]`. Use `congr 1`. Use extensionality with `L`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2, h3, -⟩, h4⟩`. Conclude with `⟨h1, h2, h3, h4⟩`. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Conclude with `⟨⟨h1, h2, h3, h4 ▸ hM⟩, h4⟩`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → ∀ (T : ℕ) (z : V) (U : Submodule K V), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → h z z = -(T : K) → U = GlobalTheory.Mass.perp h (Submodule.span K {z}) → GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes h U) → ∀ L₀ : Submodule (𝓞 K) U, GlobalTheory.Mass.IsIntLat (GlobalTheory.Mass.hRes h U) L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual (GlobalTheory.Mass.hRes h U) L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual (GlobalTheory.Mass.hRes h U) L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → ∀ φ : Submodule (𝓞 K) U → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.Mass.hRes h U)) (M : Submodule (𝓞 K) U), φ (s • M) = φ M) → GlobalTheory.Mass.orbSum (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) z) {L : Submodule (𝓞 K) V | Submodule.IsLattice K L ∧ Formalism.HermitianLatticesTheory.IsUnimodular h L ∧ (∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ GlobalTheory.Mass.latIn U L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.Mass.hRes h U) L₀} (fun L => φ (GlobalTheory.Mass.latIn U L)) = ((T - 1 : ℕ) : ℝ≥0∞) ^ Formalism.HermitianLatticesTheory.fDeg K * GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom (GlobalTheory.Mass.hRes h U)) (Formalism.HermitianLatticesTheory.genus (GlobalTheory.Mass.hRes h U) L₀) φ := by
  intro K V _ _ _ _ _ _ _ _ h hK hs T z U hT hsp hz hU' hp L₀ hL₀ e φ hφ
  have hU : ∀ v, v ∈ U ↔ h z v = 0 := by
    intro v
    rw [hU', StabSplit.mem_perp]
    refine ⟨fun H => H z (Submodule.mem_span_singleton_self z), fun H x hx => ?_⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, H, smul_zero]
  have hsU : (hRes h U).IsSymm := ⟨fun a b => hs.eq (a : V) (b : V)⟩
  have hn : (hRes h U).Nondegenerate := by
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    constructor <;>
    · intro x hx
      by_contra h0
      have := hp τ x h0
      rw [hx x] at this
      simp at this
  have hπ : ∀ (g : MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) z) (L : Submodule (𝓞 K) V),
      latIn U (g • L) = MulEquiv.ofBijective _ (resZ_bijective h hs hT hz hU) g • latIn U L :=
    fun g L => StabSplit.latIn_smul h U g.1 (smul_compl h hU g) L
  have hY := Transp.genus_stable (h := hRes h U) L₀
  rw [← Nat.cast_pow]
  refine orbSum_fibre_equiv (MulEquiv.ofBijective _ (resZ_bijective h hs hT hz hU)) _ _ (latIn U) hπ ?_ hY
    (fun L hL => hL.2.2.2) _ (fun M hM => ?_) φ hφ
  · rintro g L ⟨h1, h2, h3, h4⟩
    have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g.1.1 g.1.2 L
    refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, hπ g L ▸ hY _ _ h4⟩
    have hg : g.1.1 z = z := g.2
    rw [← h3]
    constructor
    · rintro ⟨w, hw, e'⟩
      have : w = t • z := g.1.1.injective (by rw [map_smul, hg]; exact e')
      exact this ▸ hw
    · intro hw
      exact ⟨t • z, hw, by change g.1.1 (t • z) = _; rw [map_smul, hg]⟩
  · obtain ⟨hMi, x, hx, g1, g2⟩ := cyclic_of_genus _ hK hsU hn hT hsp L₀ hL₀ e M hM
    rw [← fibre_card h hs hT hz hU hMi hx g1 g2 hK hn hsp]
    congr 1
    ext L
    constructor
    · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
      exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3, h4 ▸ hM⟩, h4⟩

end Main

end GlobalTheory.Mass.RowMean
