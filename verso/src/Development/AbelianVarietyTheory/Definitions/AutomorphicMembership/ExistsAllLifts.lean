import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstMapInjective

noncomputable section

namespace GlobalTheory.Mem.GJModel

open Formalism.BasicNotions NumberField IsDedekindDomain

/- English proof (translation)
Establish `hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible`. Take `⟨P, hP, hPl⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 B.LL) (Ideal.span {((l : ℕ) : ℤ)}) (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 B.LL)).injective_int]`. Conclude with `bot_le)`. Establish `hmem : ((l : ℕ) : 𝓞 B.LL) ∈ P`.

Establish `: ((l : ℕ) : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 B.LL))`. Rewrite using `[hPl]`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify using `using this`. Establish `hne : P ≠ ⊥`.

Introduce `h`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `hl.ne_zero (by exact_mod_cast hmem)`. Set `w : HeightOneSpectrum (𝓞 B.LL)` to `⟨P, hP.isPrime, hne⟩`. Conclude with `⟨w, Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime w) hl (Examples₂.PlacesToy.resCharW_mem w) hmem⟩`.
-/
theorem exists_place (B : Base) {l : ℕ} (hl : l.Prime) : ∃ w : B.places.Pl, B.places.resChar w = l := by
  have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 B.LL)
    (Ideal.span {((l : ℕ) : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 B.LL)).injective_int]
      exact bot_le)
  have hmem : ((l : ℕ) : 𝓞 B.LL) ∈ P := by
    have : ((l : ℕ) : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 B.LL)) := by
      rw [hPl]; exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hl.ne_zero (by exact_mod_cast hmem)
  let w : HeightOneSpectrum (𝓞 B.LL) := ⟨P, hP.isPrime, hne⟩
  exact ⟨w, Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime w) hl
    (Examples₂.PlacesToy.resCharW_mem w) hmem⟩

/- English proof (translation)
Rewrite using `[← Fintype.card_pos_iff, card_Tau B.host]`. Unfold `Ranks.f Ranks.n`. Check the signs of the components of the expression.
-/
theorem tau_nonempty (B : Base) : Nonempty (Tau B.R) := by
  rw [← Fintype.card_pos_iff, card_Tau B.host]
  unfold Ranks.f Ranks.n
  positivity

/- English proof (translation)
Take `⟨hq, hd, hq8, hd16, -⟩` from `H.hyp`. Take `⟨l, hgt, hl, hmod⟩` from `Nat.forall_exists_prime_gt_and_zmodEq (5 + H.q + H.d + H.QS) (q := 4 * H.d) (a := -1) (by have := hd.pos; omega) isCoprime_one_left.neg_left`. Establish `h4 : l % 4 = 3`. Establish `: (l : ℤ) ≡ -1 [ZMOD 4]` using `hmod.of_dvd ⟨H.d, by push_cast; ring⟩`. Unfold `Int.ModEq at this`.

Use linear arithmetic over natural numbers and integers. Establish `hd4 : H.d % 4 = 3` using `by omega`. Establish `hmd : (l : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ)` using `hmod.of_dvd ⟨4, by push_cast; ring⟩`. Establish `hj : jacobiSym (-(H.d : ℤ)) l = -1`. Rewrite using `[show (-(H.d : ℤ)) = -1 * (H.d : ℤ) by ring, jacobiSym.mul_left, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), jacobiSym.quadratic_reciprocity_three_mod_four hd4 h4, jacobiSym.mod_left' hmd, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four h4, ZMod.χ …`.

Evaluate the numerical expressions. Use `⟨l, hl, by omega, ?_⟩` and prove the remaining obligations. Establish `hs : l ∉ H.small` using `fun h => by`. Use `Nat.le_of_mem_primeFactors h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Unfold `Host.cls primeClass`. Rewrite using `[if_neg hs, if_neg (by omega), if_neg (by omega), if_neg (by rw [hj]; norm_num)]`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
theorem exists_inert {R : Ranks} (H : Host R) :
    ∃ l : ℕ, l.Prime ∧ 5 ≤ l ∧ (H.cls l = .signal ∨ H.cls l = .inertClass) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  obtain ⟨l, hgt, hl, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (5 + H.q + H.d + H.QS) (q := 4 * H.d) (a := -1)
    (by have := hd.pos; omega) isCoprime_one_left.neg_left
  have h4 : l % 4 = 3 := by
    have : (l : ℤ) ≡ -1 [ZMOD 4] := hmod.of_dvd ⟨H.d, by push_cast; ring⟩
    unfold Int.ModEq at this
    omega
  have hd4 : H.d % 4 = 3 := by omega
  have hmd : (l : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) := hmod.of_dvd ⟨4, by push_cast; ring⟩
  have hj : jacobiSym (-(H.d : ℤ)) l = -1 := by
    rw [show (-(H.d : ℤ)) = -1 * (H.d : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), jacobiSym.quadratic_reciprocity_three_mod_four hd4 h4,
      jacobiSym.mod_left' hmd, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)),
      ZMod.χ₄_nat_three_mod_four h4, ZMod.χ₄_nat_three_mod_four hd4]
    norm_num
  refine ⟨l, hl, by omega, ?_⟩
  have hs : l ∉ H.small := fun h => by
    have := Nat.le_of_mem_primeFactors h
    omega
  unfold Host.cls primeClass
  rw [if_neg hs, if_neg (by omega), if_neg (by omega), if_neg (by rw [hj]; norm_num)]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Use `choose U hU hU' using h`. Use `choose U1 hU1 hU1' using h1`. Use `choose w hw using fun i : jet.Sit => exists_place B (jet.loc i).hl.out`. Use `choose w1 hw1 using fun i : jet.Sit1 => exists_place B (jet.loc1 i).hl.out`. Take `⟨τ⟩` from `tau_nonempty B`.

Use `choose g hg hg' using fun (u : B.Word) (v : B.places.Pl) (hh : GIdx B.host (C.mem u).A.T (B.places.resChar v)) => GlobalTheory.PrescribedRank.GAtP₂ (B.places.resChar v) (Module.finrank ℂ (C.mem u).A.Mu0) hh.1`. Conclude with `⟨{ vol := vol, vol_pos := hvol, cd := cd, jet := jet, jetU := U jetL := fun i => (hU i).some, jetL' := fun i => (hU' i).some jetW := w, jetW_l := hw, jetTau := fun _ _ => τ jetW1 := w1, resChar_thetaJetPlaceDegOne := hw1, jetTau1 := fun _ => τ, jetU1 := U1 jetL1 := fun i => (hU1 …`.
-/
theorem exists_of_jet (B : Base) (C : Cols B) (vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ)
    (hvol : ∀ W, 0 < vol W) (cd : CDHaar) (jet : ThetaJet B.R B.host) (gx : GlobalExtra B.LL (Tau B.R))
    (h : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.jOf i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.jOf i)))
    (h1 : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.j1Of i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.j1Of i))) :
    ∃ G : GJStage B C, G.vol = vol ∧ G.cd = cd ∧ G.jet = jet ∧ G.gx = gx ∧
      ∀ u w h, (G.gat u w h).FinClasses := by
  choose U hU hU' using h
  choose U1 hU1 hU1' using h1
  choose w hw using fun i : jet.Sit => exists_place B (jet.loc i).hl.out
  choose w1 hw1 using fun i : jet.Sit1 => exists_place B (jet.loc1 i).hl.out
  obtain ⟨τ⟩ := tau_nonempty B
  choose g hg hg' using fun (u : B.Word) (v : B.places.Pl)
      (hh : GIdx B.host (C.mem u).A.T (B.places.resChar v)) =>
    GlobalTheory.PrescribedRank.GAtP₂ (B.places.resChar v) (Module.finrank ℂ (C.mem u).A.Mu0) hh.1
  exact ⟨{ vol := vol, vol_pos := hvol, cd := cd, jet := jet, jetU := U
           jetL := fun i => (hU i).some, jetL' := fun i => (hU' i).some
           jetW := w, jetW_l := hw, jetTau := fun _ _ => τ
           jetW1 := w1, resChar_thetaJetPlaceDegOne := hw1, jetTau1 := fun _ => τ, jetU1 := U1
           jetL1 := fun i => (hU1 i).some, jetL1' := fun i => (hU1' i).some
           gx := gx, gat := g, gat_d := hg }, rfl, rfl, rfl, rfl, hg'⟩

def gxOne (B : Base) : GlobalExtra B.LL (Tau B.R) :=
  ⟨fun _ _ => 1, fun _ _ => one_pos, fun _ => 1, fun _ => one_pos⟩

def jetOn {R : Ranks} (H : Host R) (S : Set ℕ) (hS : ∀ j ∈ S, 1 ≤ j ∧ j ≤ R.m) : ThetaJet R H where
  Sit := S
  loc := fun j =>
    haveI : Fact (exists_inert H).choose.Prime := ⟨(exists_inert H).choose_spec.1⟩
    { l := (exists_inert H).choose
      five_le_l := (exists_inert H).choose_spec.2.1
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N (j.1 - 1)
      N1 := R.N j.1
      Th := 1 }
  l_inert := fun _ => (exists_inert H).choose_spec.2.2
  jOf := fun j => j.1
  j_mem := fun j => hS j.1 j.2
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

/- English proof (translation)
Use `⟨fun ⟨G⟩ => ⟨G.cd⟩, fun ⟨cd⟩ => ?_⟩` and prove the remaining obligations. Take `⟨G, -⟩` from `exists_of_jet B C (fun _ => 1) (fun _ => one_pos) cd (jetOn B.host ∅ (fun _ h => h.elim)) (gxOne B) (fun i => i.2.elim) (fun i => i.elim)`. Conclude with `⟨G⟩`.
-/
theorem nonempty_iff (B : Base) (C : Cols B) : Nonempty (GJStage B C) ↔ Nonempty CDHaar := by
  refine ⟨fun ⟨G⟩ => ⟨G.cd⟩, fun ⟨cd⟩ => ?_⟩
  obtain ⟨G, -⟩ := exists_of_jet B C (fun _ => 1) (fun _ => one_pos) cd
    (jetOn B.host ∅ (fun _ h => h.elim)) (gxOne B) (fun i => i.2.elim) (fun i => i.elim)
  exact ⟨G⟩

/- English proof (translation)
Take `⟨G, -, hcd, hj, -, hfin⟩` from `exists_of_jet B C (fun _ => 1) (fun _ => one_pos) cd (jetOn B.host {j | 1 ≤ j ∧ j ≤ B.R.m} (fun _ h => h)) (gxOne B) (fun i => ⟨u, hu _ (le_trans (Nat.sub_le _ _) i.2.2), hu _ i.2.2⟩) (fun i => i.elim)`. Establish `hm` using `B.R.two_le_m`. Use `⟨G, hcd, ?_, ?_, hfin⟩` and prove the remaining obligations. Rewrite using `[hj]; exact ⟨⟨1, le_rfl, by omega⟩⟩`. Rewrite using `[hj]`.

Conclude with `fun j h1 h2 => ⟨⟨j, h1, h2⟩, rfl⟩`.
-/
theorem exists_all_lifts (B : Base) (C : Cols B) (cd : CDHaar) (u : B.Word)
    (hu : ∀ j, j ≤ B.R.m → Nonempty ((C.mem u).C.cls j)) :
    ∃ G : GJStage B C, G.cd = cd ∧ Nonempty G.jet.Sit ∧
      (∀ j, 1 ≤ j → j ≤ B.R.m → ∃ i, G.jet.jOf i = j) ∧ ∀ u w h, (G.gat u w h).FinClasses := by
  obtain ⟨G, -, hcd, hj, -, hfin⟩ := exists_of_jet B C (fun _ => 1) (fun _ => one_pos) cd
    (jetOn B.host {j | 1 ≤ j ∧ j ≤ B.R.m} (fun _ h => h)) (gxOne B)
    (fun i => ⟨u, hu _ (le_trans (Nat.sub_le _ _) i.2.2), hu _ i.2.2⟩) (fun i => i.elim)
  have hm := B.R.two_le_m
  refine ⟨G, hcd, ?_, ?_, hfin⟩
  · rw [hj]; exact ⟨⟨1, le_rfl, by omega⟩⟩
  · rw [hj]; exact fun j h1 h2 => ⟨⟨j, h1, h2⟩, rfl⟩

/- English proof (translation)
Use `⟨⟨G.jetL i⟩, ⟨G.jetL' i⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[G.jetW_l]`. Conclude with `(G.jet.loc i).five_le_l`. Rewrite using `[G.jetW_l]`. Conclude with `G.jet.l_inert i`.
-/
theorem sit_spec {B : Base} {C : Cols B} (G : GJStage B C) (i : G.jet.Sit) :
    Nonempty ((C.mem (G.jetU i)).C.cls (G.jet.jOf i - 1)) ∧ Nonempty ((C.mem (G.jetU i)).C.cls (G.jet.jOf i)) ∧
      5 ≤ B.places.resChar (G.jetW i) ∧
      (B.host.cls (B.places.resChar (G.jetW i)) = .signal ∨ B.host.cls (B.places.resChar (G.jetW i)) = .inertClass) := by
  refine ⟨⟨G.jetL i⟩, ⟨G.jetL' i⟩, ?_, ?_⟩
  · rw [G.jetW_l]; exact (G.jet.loc i).five_le_l
  · rw [G.jetW_l]; exact G.jet.l_inert i

end GlobalTheory.Mem.GJModel

end
