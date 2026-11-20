import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SmallAllPf

variable {D : D7}

/- English proof (translation)
Establish `hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P`. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hP, rest⟩`. Conclude with `⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩`. Conclude with `⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩`.
-/
theorem vac_at_place {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    {f : WO S T → ℂ} (h : Vac ψ S T LS LT P f) {v : Pl D} (hv : P v) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨α, hα, hP, rest⟩
    exact ⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

/- English proof (translation)
Introduce `D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ`. Establish `hSO` using `GlobalTheory.T.smallPair_pairing_at_one_gluedPlace D`. Establish `hOB` using `GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D`. Establish `hAB` using `GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D`. Use `choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)`.

Use `⟨r, e, hr, ?_⟩` and prove the remaining obligations. Introduce `ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF`. Establish `hstd : IsStdChar D ψ (-1)` using `hom₁.std`. Establish `hinj : Function.Injective fun i => (p i).v` using `hP.inj`. Establish `hPi : ∀ i, P (p i).v` using `fun i => (hP.mem _).2 ⟨i, rfl⟩`.

Use `set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc`. Use `set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ := fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ`. Establish `keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ), OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f'`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil`. Introduce `f f' h i _ hv`. Establish `h' : f' = f` using `h`. Rewrite using `[h']`. Conclude with `hv`.

Consider the case `cons j l ih`. Introduce `f f' h i hi hv`. Take `⟨g, hg, hOj⟩` from `h`. Establish `hgv` using `ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv`. Establish `hij : i ≠ j` using `fun e => hi (e ▸ List.mem_cons_self)`.

Conclude with `((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _ hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv`. Establish `val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ), (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ → ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F = (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) …`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`.

Introduce `_ Ξ₀ Ξ₁ _ h φ _`. Establish `h' : Ξ₁ = Ξ₀` using `h`. Substitute `h'` using the available equality. Simplify using `[PairDat.sAll]`. Consider the case `cons j l ih`.

Introduce `hnd Ξ₀ Ξ₁ h1 h φ hφ`. Take `⟨g, hg, hOj⟩` from `h`. Establish `hj : j ∉ l` using `(List.nodup_cons.1 hnd).1`. Establish `hgv` using `keep l Ξ₀ g hg j hj (h1 j)`. Rewrite using `[ih hnd.tail Ξ₀ g h1 hg φ hφ]`.

Establish `hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ)` using `(hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ`. Establish `hself` using `(hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2 (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2`. Take `⟨u1, u2, u3, u4⟩` from `hunr _ (hPi j)`. Establish `key` using `hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃ (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF`. Establish `hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ = sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j) (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ)` using `rfl`.

Rewrite using `[key, hcons, List.map_cons, List.prod_cons, hc]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ`.
-/
theorem main : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ
  have hSO := GlobalTheory.T.smallPair_pairing_at_one_gluedPlace D
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have hAB := GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D
  choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)
  refine ⟨r, e, hr, ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc
    Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF
  have hstd : IsStdChar D ψ (-1) := hom₁.std
  have hinj : Function.Injective fun i => (p i).v := hP.inj
  have hPi : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc
  set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ :=
    fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ

  have keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ),
      OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f →
        Vac ψ V₀ S L₁ L₂ (· = (p i).v) f' := by
    intro l
    induction l with
    | nil =>
      intro f f' h i _ hv
      have h' : f' = f := h
      rw [h']
      exact hv
    | cons j l ih =>
      intro f f' h i hi hv
      obtain ⟨g, hg, hOj⟩ := h
      have hgv := ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv
      have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      exact ((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _
        hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv
  have val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ),
      (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ →
      ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F =
        (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) Ξ₁ Φ₂ F := by
    intro l
    induction l with
    | nil =>
      intro _ Ξ₀ Ξ₁ _ h φ _
      have h' : Ξ₁ = Ξ₀ := h
      subst h'
      simp [PairDat.sAll]
    | cons j l ih =>
      intro hnd Ξ₀ Ξ₁ h1 h φ hφ
      obtain ⟨g, hg, hOj⟩ := h
      have hj : j ∉ l := (List.nodup_cons.1 hnd).1
      have hgv := keep l Ξ₀ g hg j hj (h1 j)
      rw [ih hnd.tail Ξ₀ g h1 hg φ hφ]
      have hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) :=
        (hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ
      have hself := (hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2
        (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2
      obtain ⟨u1, u2, u3, u4⟩ := hunr _ (hPi j)
      have key := hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT
        (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃
        (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF
      have hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ =
          sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j)
            (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) := rfl
      rw [key, hcons, List.map_cons, List.prod_cons, hc]
      ring
  exact val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ

end GlobalTheory.FinPl.SmallAllPf

end
