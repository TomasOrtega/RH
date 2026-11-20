import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Rewrite `hf`, the goal using `[GroundTheory.Automorphic.mem_locallyConstantCompactSupport]`. Use `⟨hf.1.comp_continuous (continuous_mul_right u), ?_⟩` and prove the remaining obligations. Conclude with `hf.2.comp_homeomorph (Homeomorph.mulRight u)`.
-/
private theorem mem_Cc_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {f : G → ℂ} (hf : f ∈ Cc G) (u : G) : (fun x => f (x * u)) ∈ Cc G := by
  rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  refine ⟨hf.1.comp_continuous (continuous_mul_right u), ?_⟩
  exact hf.2.comp_homeomorph (Homeomorph.mulRight u)

@[reducible] private def act {G : Type} [Group G] (B N : Subgroup G) : MulAction (B × N) G where
  smul h g := (h.1 : G) * g * (h.2 : G)⁻¹
  one_smul g := by
    show ((1 : B × N).1 : G) * g * ((1 : B × N).2 : G)⁻¹ = g
    simp
  mul_smul h k g := by
    show ((h * k).1 : G) * g * ((h * k).2 : G)⁻¹ =
      (h.1 : G) * ((k.1 : G) * g * (k.2 : G)⁻¹) * (h.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
    group

/- English proof (translation)
Use `letI := act B N`. Use `show orbit (B × N) w = cell B N w`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨b, u⟩, rfl⟩`.

Conclude with `⟨b, b.2, (u : G)⁻¹, N.inv_mem u.2, rfl⟩`. Introduce and unpack `⟨b, hb, u, hu, rfl⟩`. Use `⟨(⟨b, hb⟩, ⟨u, hu⟩⁻¹), ?_⟩` and prove the remaining obligations. Use `show b * w * (((⟨u, hu⟩⁻¹ : N) : G))⁻¹ = b * w * u`. Simplify using the standard rewrite rules.
-/
private theorem orbit_act {G : Type} [Group G] (B N : Subgroup G) (w : G) :
    letI := act B N; orbit (B × N) w = cell B N w := by
  letI := act B N
  show orbit (B × N) w = cell B N w
  ext g
  constructor
  · rintro ⟨⟨b, u⟩, rfl⟩
    exact ⟨b, b.2, (u : G)⁻¹, N.inv_mem u.2, rfl⟩
  · rintro ⟨b, hb, u, hu, rfl⟩
    refine ⟨(⟨b, hb⟩, ⟨u, hu⟩⁻¹), ?_⟩
    show b * w * (((⟨u, hu⟩⁻¹ : N) : G))⁻¹ = b * w * u
    simp

/- English proof (translation)
Introduce `hD G _ _ _ _ _ _ _ B N hB hN s p hp hs hsp hsB hsN hC η θ hη hθ hηs hθs D hDB hDN f hf`. Take `⟨L, hLo, hL⟩` from `hη`. Take `⟨k, w, hw1, hw2, hw3⟩` from `hC`. Use `letI := act B N`. Use `haveI : LocallyCompactSpace B := hB.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace N := hN.locallyCompactSpace`. Use `haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaCompactSpace (B × N) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : ContinuousSMul (B × N) G := ⟨by show Continuous fun q : (B × N) × G => (q.1.1 : G) * q.2 * (q.1.2 : G)⁻¹`.

Conclude with `((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv⟩`. Set `sB : B →* B` to `(s.comp B.subtype).codRestrict B (fun b => hsB b b.2)`. Set `sN : N →* N` to `(s.comp N.subtype).codRestrict N (fun u => hsN u u.2)`. Set `τ : B × N →* B × N` to `sB.prodMap sN`. Establish `hτc : Continuous τ`.

Rewrite using `[MonoidHom.coe_prodMap]`. Conclude with `(Continuous.subtype_mk (hs.comp continuous_subtype_val) _).prodMap (Continuous.subtype_mk (hs.comp continuous_subtype_val) _)`. Establish `hit : ∀ n (h : B × N), ((τ^[n] h).1 : G) = s^[n] h.1 ∧ ((τ^[n] h).2 : G) = s^[n] h.2`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro h`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `h`. Simplify using `only [Function.iterate_succ_apply']`.

Conclude with `⟨by rw [← (ih h).1]; rfl, by rw [← (ih h).2]; rfl⟩`. Set `χ : B × N →* ℂ` to `(η.comp (MonoidHom.fst B N)) * ((Units.coeHom ℂ).comp (θ.comp (MonoidHom.snd B N)))`. Establish `hχ : ∀ h : B × N, χ h = η h.1 * (θ h.2 : ℂ)` using `fun h => rfl`. Use `hD G (B × N) s τ p hp hs hτc hsp ?_ ?_ χ ?_ ?_ k w hw1 ?_ ?_ D ?_ f hf` and prove the remaining obligations. Introduce `h`.

Use `hit p h` as an intermediate fact. Conclude with `Prod.ext (Subtype.ext (this.1.trans (hsp _))) (Subtype.ext (this.2.trans (hsp _)))`. Introduce `h x show s ((h.1 : G) * x * (h.2 : G)⁻¹) = s h.1 * s x * (s h.2)⁻¹`. Simplify using `[map_mul, map_inv]`. Use `⟨(L.comap B.subtype).prod θ.ker, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_prod]`. Conclude with `(hLo.preimage continuous_subtype_val).prod hθ`. Introduce `l hl`. Rewrite `hl` using `[Subgroup.mem_prod]`. Rewrite using `[hχ, hL l.1 hl.1, MonoidHom.mem_ker.1 hl.2]`.

Simplify using the standard rewrite rules. Introduce `h`. Rewrite using `[hχ, hχ, hηs h.1 (τ h).1 rfl, hθs h.2 (τ h).2 rfl]`. Introduce `y`. Simplify `hw2 y` using `only [orbit_act]`.

Introduce `j`. Simplify `hw3 j` using `only [orbit_act]`. Introduce `h g hg`. Establish `hg' : (fun x => g (x * (h.2 : G))) ∈ Cc G` using `mem_Cc_mul_right hg _`. Establish `e : GroundTheory.Automorphic.Whittaker.transl h g = fun x => (fun y => g (y * (h.2 : G))) ((h.1 : G)⁻¹ * x)`.

Use function extensionality and compare the values at `x`. Use `show g (((h⁻¹).1 : G) * x * ((h⁻¹).2 : G)⁻¹) = g ((h.1 : G)⁻¹ * x * h.2)`. Simplify using the standard rewrite rules. Rewrite using `[e, hDB h.1 _ hg', hDN h.2 g hg, hχ, mul_assoc]`.
-/
theorem UpperTheory.Gal.LocD.biInv :
    DistInv → BiInv := by
  intro hD G _ _ _ _ _ _ _ B N hB hN s p hp hs hsp hsB hsN hC η θ hη hθ hηs hθs D hDB hDN f hf
  obtain ⟨L, hLo, hL⟩ := hη
  obtain ⟨k, w, hw1, hw2, hw3⟩ := hC
  letI := act B N
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (B × N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ContinuousSMul (B × N) G := ⟨by
    show Continuous fun q : (B × N) × G => (q.1.1 : G) * q.2 * (q.1.2 : G)⁻¹
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv⟩
  let sB : B →* B := (s.comp B.subtype).codRestrict B (fun b => hsB b b.2)
  let sN : N →* N := (s.comp N.subtype).codRestrict N (fun u => hsN u u.2)
  let τ : B × N →* B × N := sB.prodMap sN
  have hτc : Continuous τ := by
    rw [MonoidHom.coe_prodMap]
    exact (Continuous.subtype_mk (hs.comp continuous_subtype_val) _).prodMap
      (Continuous.subtype_mk (hs.comp continuous_subtype_val) _)
  have hit : ∀ n (h : B × N), ((τ^[n] h).1 : G) = s^[n] h.1 ∧ ((τ^[n] h).2 : G) = s^[n] h.2 := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      simp only [Function.iterate_succ_apply']
      exact ⟨by rw [← (ih h).1]; rfl, by rw [← (ih h).2]; rfl⟩
  let χ : B × N →* ℂ := (η.comp (MonoidHom.fst B N)) * ((Units.coeHom ℂ).comp (θ.comp (MonoidHom.snd B N)))
  have hχ : ∀ h : B × N, χ h = η h.1 * (θ h.2 : ℂ) := fun h => rfl
  refine hD G (B × N) s τ p hp hs hτc hsp ?_ ?_ χ ?_ ?_ k w hw1 ?_ ?_ D ?_ f hf
  · intro h
    have := hit p h
    exact Prod.ext (Subtype.ext (this.1.trans (hsp _))) (Subtype.ext (this.2.trans (hsp _)))
  · intro h x
    show s ((h.1 : G) * x * (h.2 : G)⁻¹) = s h.1 * s x * (s h.2)⁻¹
    simp [map_mul, map_inv]
  · refine ⟨(L.comap B.subtype).prod θ.ker, ?_, ?_⟩
    · rw [Subgroup.coe_prod]
      exact (hLo.preimage continuous_subtype_val).prod hθ
    · intro l hl
      rw [Subgroup.mem_prod] at hl
      rw [hχ, hL l.1 hl.1, MonoidHom.mem_ker.1 hl.2]
      simp
  · intro h
    rw [hχ, hχ, hηs h.1 (τ h).1 rfl, hθs h.2 (τ h).2 rfl]
  · intro y
    simpa only [orbit_act] using hw2 y
  · intro j
    simpa only [orbit_act] using hw3 j
  · intro h g hg
    have hg' : (fun x => g (x * (h.2 : G))) ∈ Cc G := mem_Cc_mul_right hg _
    have e : GroundTheory.Automorphic.Whittaker.transl h g = fun x => (fun y => g (y * (h.2 : G))) ((h.1 : G)⁻¹ * x) := by
      funext x
      show g (((h⁻¹).1 : G) * x * ((h⁻¹).2 : G)⁻¹) = g ((h.1 : G)⁻¹ * x * h.2)
      simp
    rw [e, hDB h.1 _ hg', hDN h.2 g hg, hχ, mul_assoc]
