import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RebaseProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section One

variable {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : Frame p S n'} {β : Frame p T n}

/- English proof (translation)
Establish `hb` using `(GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f hf).2.2 hu ΛS ΛT hS hT`. Conclude with `(GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS NS' NT NT' h1 h2 h3 h4).1 ΛS ΛT hS' hT' f f hb`.
-/
theorem cc (hstd : IsStdChar D ψ (-1)) (hu : p.UnitAA) {NS NS' : Lat S} {NT NT' : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S NS') (h4 : IsSelfDualC T NT')
    {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)} (hS : α.IsLat NS ΛS) (hS' : α.IsLat NS' ΛS)
    (hT : β.IsLat NT ΛT) (hT' : β.IsLat NT' ΛT) {f : WO S T → ℂ} (hf : Vac ψ S T NS NT (· = p.v) f) :
    Vac ψ S T NS' NT' (· = p.v) f ∧ ∀ Ψ h, Over ψ α β NS NT f Ψ h → Over ψ α β NS' NT' f Ψ h := by
  have hb := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f hf).2.2 hu ΛS ΛT hS hT
  exact (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS NS' NT NT' h1 h2 h3 h4).1 ΛS ΛT hS' hT' f f hb

/- English proof (translation)
Establish `R` using `(GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS N'S NT N'T h1 h2 h3 h4).1 A'S A'T hA'S hA'T f₀ g hg`. Use `⟨R.1, fun Ψ h => ⟨R.2 Ψ h, fun hh => ?_⟩⟩` and prove the remaining obligations. Take `⟨g', hg', huniq⟩` from `(GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β N'S N'T h3 h4 g R.1).1 (latInd AS AT) (latInd_mem_SB AS AT)`. Establish `R'` using `(GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β N'S NS N'T NT h3 h4 h1 h2).1 AS AT hAS hAT g g' hg'`. Establish `hself` using `(GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f₀ hf₀).2.2 hu AS AT hAS hAT`.

Establish `he : f₀ = g'` using `huniq f₀ (R.2 _ _ hself)`. Rewrite using `[he]`. Conclude with `R'.2 Ψ h hh`.
-/
theorem sp1 (hstd : IsStdChar D ψ (-1)) (hu : p.UnitAA) {NS N'S : Lat S} {NT N'T : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S N'S) (h4 : IsSelfDualC T N'T)
    {AS A'S : Submodule 𝒪[k] (n' → k)} {AT A'T : Submodule 𝒪[k] (n → k)} [AS.IsLattice k] [AT.IsLattice k]
    (hAS : α.IsLat NS AS) (hAT : β.IsLat NT AT) (hA'S : α.IsLat N'S A'S) (hA'T : β.IsLat N'T A'T)
    {f₀ g : WO S T → ℂ} (hf₀ : Vac ψ S T NS NT (· = p.v) f₀) (hg : Over ψ α β NS NT f₀ (latInd A'S A'T) g) :
    Vac ψ S T N'S N'T (· = p.v) g ∧ ∀ Ψ h, Over ψ α β NS NT f₀ Ψ h ↔ Over ψ α β N'S N'T g Ψ h := by
  have R := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS N'S NT N'T h1 h2 h3 h4).1 A'S A'T hA'S hA'T f₀ g hg
  refine ⟨R.1, fun Ψ h => ⟨R.2 Ψ h, fun hh => ?_⟩⟩
  obtain ⟨g', hg', huniq⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β N'S N'T h3 h4 g R.1).1 (latInd AS AT)
    (latInd_mem_SB AS AT)
  have R' := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β N'S NS N'T NT h3 h4 h1 h2).1 AS AT hAS hAT g g' hg'
  have hself := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f₀ hf₀).2.2 hu AS AT hAS hAT
  have he : f₀ = g' := huniq f₀ (R.2 _ _ hself)
  rw [he]
  exact R'.2 Ψ h hh

end One

section Chain

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro f f' hf`. Conclude with `hf`. Consider the case `cons i l ih`. Introduce `f f' hf`.

Take `⟨g, hg, hO⟩` from `ValDbl.overAll_cons.1 hf`. Use `ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) f g hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← h i List.mem_cons_self]`. Conclude with `hO`.
-/
theorem overAll_congrΨ {LS : Lat S} {LT : Lat T} {Ψ Ψ' : ι → Matrix n n' k → ℂ} (l : List ι)
    (h : ∀ j ∈ l, Ψ j = Ψ' j) : ∀ f f', OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β LS LT Ψ' l f f' := by
  induction l with
  | nil => intro f f' hf; exact hf
  | cons i l ih =>
    intro f f' hf
    obtain ⟨g, hg, hO⟩ := ValDbl.overAll_cons.1 hf
    refine ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) f g hg, ?_⟩
    rw [← h i List.mem_cons_self]
    exact hO

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro f f' hf`. Conclude with `hf`. Consider the case `cons i l ih`. Introduce `f f' hf`.

Take `⟨g, hg, hO⟩` from `ValDbl.overAll_cons.1 hf`. Take `⟨ΛS, ΛT, a, b, c, d⟩` from `hsame i List.mem_cons_self`. Conclude with `ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => hsame j (List.mem_cons_of_mem _ hj)) f g hg, (cc hstd (hunit i) h1 h2 h3 h4 a b c d hO.2.2.1).2 _ _ hO⟩`.
-/
theorem overAll_congr (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) {NS NS' : Lat S} {NT NT' : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S NS') (h4 : IsSelfDualC T NT')
    {Ψ : ι → Matrix n n' k → ℂ} (l : List ι)
    (hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat NS ΛS ∧ (α j).IsLat NS' ΛS ∧ (β j).IsLat NT ΛT ∧ (β j).IsLat NT' ΛT) :
    ∀ f f', OverAll ψ α β NS NT Ψ l f f' → OverAll ψ α β NS' NT' Ψ l f f' := by
  induction l with
  | nil => intro f f' hf; exact hf
  | cons i l ih =>
    intro f f' hf
    obtain ⟨g, hg, hO⟩ := ValDbl.overAll_cons.1 hf
    obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame i List.mem_cons_self
    exact ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => hsame j (List.mem_cons_of_mem _ hj)) f g hg,
      (cc hstd (hunit i) h1 h2 h3 h4 a b c d hO.2.2.1).2 _ _ hO⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ValDbl.overAll_nil.2 rfl`. Consider the case `cons i l ih`. Conclude with `ValDbl.overAll_cons.2 ⟨f, ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)), (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hstd S T (α i) (β i) NS NT h1 h2 f (hf i List.mem_cons_self)).2.2 (hunit i) (AS i) (AT i) (hA i).1 (hA i).2⟩`.
-/
theorem overAll_self (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) {NS : Lat S} {NT : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) {AS : ι → Submodule 𝒪[k] (n' → k)}
    {AT : ι → Submodule 𝒪[k] (n → k)} (hA : ∀ j, (α j).IsLat NS (AS j) ∧ (β j).IsLat NT (AT j)) (f : WO S T → ℂ)
    (l : List ι) (hf : ∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) f) :
    OverAll ψ α β NS NT (fun j => latInd (AS j) (AT j)) l f f := by
  induction l with
  | nil => exact ValDbl.overAll_nil.2 rfl
  | cons i l ih =>
    exact ValDbl.overAll_cons.2 ⟨f, ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)),
      (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hstd S T (α i) (β i) NS NT h1 h2 f (hf i List.mem_cons_self)).2.2 (hunit i)
        (AS i) (AT i) (hA i).1 (hA i).2⟩

variable {NS : Lat S} {NT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce and unpack `f' ⟨h, hh, hO⟩`. Rewrite `hO` using `[ValDbl.overAll_nil.1 hh]`. Conclude with `⟨f', hO, ValDbl.overAll_nil.2 rfl⟩`.

Consider the case `cons j l ih`. Introduce and unpack `f' ⟨h, hh, hO⟩`. Establish `hij : i ≠ j` using `fun e => hil (e ▸ List.mem_cons_self)`. Establish `hil' : i ∉ l` using `fun h' => hil (List.mem_cons_of_mem _ h')`. Take `⟨m, hm, hmO⟩` from `ValDbl.overAll_cons.1 hh`.

Establish `hmv` using `ValDbl.overAll_vac hstd hinj l b m hm i hil' hb`. Take `⟨g', hg'1, hg'2⟩` from `GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p j) (p i) n n' n n' ψ hstd (hunit j) (hunit i) (fun e => hij (hinj e.symm)) S T (α j) (β j) (α i) (β i) NS NT m h f' (Ψ j) (Ψ i) hmv hmO hO`. Take `⟨k', hk', hl⟩` from `ih hil' g' ⟨m, hm, hg'1⟩`. Conclude with `⟨k', hk', ValDbl.overAll_cons.2 ⟨g', hl, hg'2⟩⟩`.
-/
theorem swap_fwd (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (i : ι) (l : List ι) (hil : i ∉ l) (b : WO S T → ℂ) (hb : Vac ψ S T NS NT (· = (p i).v) b) :
    ∀ f', (∃ h, OverAll ψ α β NS NT Ψ l b h ∧ Over ψ (α i) (β i) NS NT h (Ψ i) f') →
      ∃ k', Over ψ (α i) (β i) NS NT b (Ψ i) k' ∧ OverAll ψ α β NS NT Ψ l k' f' := by
  induction l with
  | nil =>
    rintro f' ⟨h, hh, hO⟩
    rw [ValDbl.overAll_nil.1 hh] at hO
    exact ⟨f', hO, ValDbl.overAll_nil.2 rfl⟩
  | cons j l ih =>
    rintro f' ⟨h, hh, hO⟩
    have hij : i ≠ j := fun e => hil (e ▸ List.mem_cons_self)
    have hil' : i ∉ l := fun h' => hil (List.mem_cons_of_mem _ h')
    obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 hh
    have hmv := ValDbl.overAll_vac hstd hinj l b m hm i hil' hb
    obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p j) (p i) n n' n n' ψ hstd (hunit j) (hunit i)
      (fun e => hij (hinj e.symm)) S T (α j) (β j) (α i) (β i) NS NT m h f' (Ψ j) (Ψ i) hmv hmO hO
    obtain ⟨k', hk', hl⟩ := ih hil' g' ⟨m, hm, hg'1⟩
    exact ⟨k', hk', ValDbl.overAll_cons.2 ⟨g', hl, hg'2⟩⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce and unpack `f' ⟨k', hk', hl⟩`. Rewrite using `[ValDbl.overAll_nil.1 hl]`. Conclude with `⟨b, ValDbl.overAll_nil.2 rfl, hk'⟩`.

Consider the case `cons j l ih`. Introduce and unpack `f' ⟨k', hk', hl⟩`. Rewrite `hnd` using `[List.nodup_cons]`. Establish `hij : i ≠ j` using `fun e => hil (e ▸ List.mem_cons_self)`. Establish `hil' : i ∉ l` using `fun h' => hil (List.mem_cons_of_mem _ h')`.

Take `⟨m, hm, hmO⟩` from `ValDbl.overAll_cons.1 hl`. Take `⟨h₀, hh₀, hO₀⟩` from `ih hnd.2 hil' (fun j' hj' => hb j' (List.mem_cons_of_mem _ hj')) m ⟨k', hk', hm⟩`. Establish `hv` using `ValDbl.overAll_vac hstd hinj l b h₀ hh₀ j hnd.1 (hb j List.mem_cons_self)`. Take `⟨g', hg'1, hg'2⟩` from `GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j) (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) NS NT h₀ m f' (Ψ i) (Ψ j) hv hO₀ hmO`. Conclude with `⟨g', ValDbl.overAll_cons.2 ⟨h₀, hh₀, hg'1⟩, hg'2⟩`.
-/
theorem swap_bwd (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (i : ι) (l : List ι) (hnd : l.Nodup) (hil : i ∉ l) (b : WO S T → ℂ)
    (hb : ∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) b) :
    ∀ f', (∃ k', Over ψ (α i) (β i) NS NT b (Ψ i) k' ∧ OverAll ψ α β NS NT Ψ l k' f') →
      ∃ h, OverAll ψ α β NS NT Ψ l b h ∧ Over ψ (α i) (β i) NS NT h (Ψ i) f' := by
  induction l with
  | nil =>
    rintro f' ⟨k', hk', hl⟩
    rw [ValDbl.overAll_nil.1 hl]
    exact ⟨b, ValDbl.overAll_nil.2 rfl, hk'⟩
  | cons j l ih =>
    rintro f' ⟨k', hk', hl⟩
    rw [List.nodup_cons] at hnd
    have hij : i ≠ j := fun e => hil (e ▸ List.mem_cons_self)
    have hil' : i ∉ l := fun h' => hil (List.mem_cons_of_mem _ h')
    obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 hl
    obtain ⟨h₀, hh₀, hO₀⟩ := ih hnd.2 hil' (fun j' hj' => hb j' (List.mem_cons_of_mem _ hj')) m ⟨k', hk', hm⟩
    have hv := ValDbl.overAll_vac hstd hinj l b h₀ hh₀ j hnd.1 (hb j List.mem_cons_self)
    obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j)
      (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) NS NT h₀ m f' (Ψ i) (Ψ j) hv hO₀ hmO
    exact ⟨g', ValDbl.overAll_cons.2 ⟨h₀, hh₀, hg'1⟩, hg'2⟩

end Chain

section Front

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
  {Ψ : ι → Matrix n n' k → ℂ}

/- English proof (translation)
Establish `hsp` using `sp1 hstd (hunit i) h1 h2 h3 h4 hAS hAT hA'S hA'T hg₁i hO`. Establish `hsame' : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), (α j).IsLat N'S ΛS ∧ (α j).IsLat N₁S ΛS ∧ (β j).IsLat N'T ΛT ∧ (β j).IsLat N₁T ΛT` using `fun j hj => by`. Take `⟨ΛS, ΛT, a, b, c, d⟩` from `hsame j hj`. Conclude with `⟨ΛS, ΛT, b, a, d, c⟩`. Introduce `f'`.

Prove the components needed by the constructor for the conclusion. Introduce `hL`. Take `⟨k', hk', hl⟩` from `swap_fwd hstd hunit hinj i l hil g₁ hg₁i f' (ValDbl.overAll_cons.1 hL)`. Conclude with `ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g hg f' ⟨k', (hsp.2 _ _).1 hk', overAll_congr hstd hunit h1 h2 h3 h4 l hsame k' f' hl⟩)`. Introduce `hR`.

Take `⟨k', hk', hl⟩` from `swap_fwd hstd hunit hinj i l hil g hsp.1 f' (ValDbl.overAll_cons.1 hR)`. Conclude with `ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g₁ hg₁ f' ⟨k', (hsp.2 _ _).2 hk', overAll_congr hstd hunit h3 h4 h1 h2 l hsame' k' f' hl⟩)`.
-/
theorem front (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    {N₁S N'S : Lat S} {N₁T N'T : Lat T} (h1 : IsSelfDualC S N₁S) (h2 : IsSelfDualC T N₁T) (h3 : IsSelfDualC S N'S)
    (h4 : IsSelfDualC T N'T) (i : ι) (l : List ι) (hnd : l.Nodup) (hil : i ∉ l)
    {AS A'S : Submodule 𝒪[k] (n' → k)} {AT A'T : Submodule 𝒪[k] (n → k)} [AS.IsLattice k] [AT.IsLattice k]
    (hAS : (α i).IsLat N₁S AS) (hAT : (β i).IsLat N₁T AT) (hA'S : (α i).IsLat N'S A'S) (hA'T : (β i).IsLat N'T A'T)
    (hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat N₁S ΛS ∧ (α j).IsLat N'S ΛS ∧ (β j).IsLat N₁T ΛT ∧ (β j).IsLat N'T ΛT)
    {g₁ g : WO S T → ℂ} (hg₁i : Vac ψ S T N₁S N₁T (· = (p i).v) g₁)
    (hg₁ : ∀ j ∈ l, Vac ψ S T N₁S N₁T (· = (p j).v) g₁) (hg : ∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g)
    (hO : Over ψ (α i) (β i) N₁S N₁T g₁ (latInd A'S A'T) g) :
    ∀ f', OverAll ψ α β N₁S N₁T Ψ (i :: l) g₁ f' ↔ OverAll ψ α β N'S N'T Ψ (i :: l) g f' := by
  have hsp := sp1 hstd (hunit i) h1 h2 h3 h4 hAS hAT hA'S hA'T hg₁i hO
  have hsame' : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat N'S ΛS ∧ (α j).IsLat N₁S ΛS ∧ (β j).IsLat N'T ΛT ∧ (β j).IsLat N₁T ΛT := fun j hj => by
    obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame j hj
    exact ⟨ΛS, ΛT, b, a, d, c⟩
  intro f'
  constructor
  · intro hL
    obtain ⟨k', hk', hl⟩ := swap_fwd hstd hunit hinj i l hil g₁ hg₁i f' (ValDbl.overAll_cons.1 hL)
    exact ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g hg f'
      ⟨k', (hsp.2 _ _).1 hk', overAll_congr hstd hunit h1 h2 h3 h4 l hsame k' f' hl⟩)
  · intro hR
    obtain ⟨k', hk', hl⟩ := swap_fwd hstd hunit hinj i l hil g hsp.1 f' (ValDbl.overAll_cons.1 hR)
    exact ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g₁ hg₁ f'
      ⟨k', (hsp.2 _ _).2 hk', overAll_congr hstd hunit h3 h4 h1 h2 l hsame' k' f' hl⟩)

end Front

section Gen

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}

open Classical in

/- English proof (translation)
Establish `hunit` using `hPl.unit`. Establish `hinj` using `hPl.inj`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_ NS N'S NT N'T AS A'S AT A'T _ _ _ _ _ _ _ f g _ hg`.

Rewrite using `[ValDbl.overAll_nil.1 hg]`. Conclude with `⟨fun j hj => by simp at hj, fun Ψ f' => Iff.rfl⟩`. Consider the case `cons i l ih`. Introduce `hl NS N'S NT N'T AS A'S AT A'T h1 h2 h3 h4 hL hA hout f g hf hg`. Rewrite `hl` using `[List.nodup_cons]`.

Take `⟨hil, hnd⟩` from `hl`. Set `BS : ι → Submodule 𝒪[k] (n' → k)` to `fun j => if j ∈ l then A'S j else AS j`. Set `BT : ι → Submodule 𝒪[k] (n → k)` to `fun j => if j ∈ l then A'T j else AT j`. Establish `hBS : ∀ j, (BS j).IsLattice k` using `fun j => by`. Distinguish the cases in `hj : j ∈ l`.

Simplify using `only [BS, if_pos hj]`. Conclude with `(hL j).2.1`. Simplify using `only [BS, if_neg hj]`. Conclude with `(hL j).1`. Establish `hBT : ∀ j, (BT j).IsLattice k` using `fun j => by`.

Distinguish the cases in `hj : j ∈ l`. Simplify using `only [BT, if_pos hj]`. Conclude with `(hL j).2.2.2`. Simplify using `only [BT, if_neg hj]`. Conclude with `(hL j).2.2.1`.

Take `⟨N₁S, hN₁S, hlatS, -⟩` from `GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n' S α NS h1 BS hBS`. Take `⟨N₁T, hN₁T, hlatT, -⟩` from `GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n T β NT h2 BT hBT`. Take `⟨g₁, hg₁, hO⟩` from `ValDbl.overAll_cons.1 hg`. Establish `hg₁' : OverAll ψ α β NS NT (fun j => latInd (BS j) (BT j)) l f g₁` using `overAll_congrΨ l (fun j hj => by simp only [BS, BT, if_pos hj]) f g₁ hg₁`. Establish `IH` using `ih hnd NS N₁S NT N₁T AS BS AT BT h1 h2 hN₁S hN₁T (fun j => ⟨(hL j).1, hBS j, (hL j).2.2.1, hBT j⟩) (fun j => ⟨(hA j).1, hlatS j, (hA j).2.2.1, hlatT j⟩) (fun j hj => ⟨by simp only [BS, if_neg hj], by simp only [BT, if_neg hj]⟩) f g₁ (fun j hj => hf j (List.mem_cons_of_mem _ hj)) …`.

Establish `hBi : BS i = AS i ∧ BT i = AT i` using `⟨by simp only [BS, if_neg hil], by simp only [BT, if_neg hil]⟩`. Establish `hN₁Si : (α i).IsLat N₁S (AS i)` using `hBi.1 ▸ hlatS i`. Establish `hN₁Ti : (β i).IsLat N₁T (AT i)` using `hBi.2 ▸ hlatT i`. Establish `hg₁v : Vac ψ S T NS NT (· = (p i).v) g₁` using `ValDbl.overAll_vac hstd hinj l f g₁ hg₁ i hil (hf i List.mem_cons_self)`. Establish `C` using `cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hg₁v`.

Establish `hO₁` using `C.2 _ _ hO`. Establish `hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), (α j).IsLat N₁S ΛS ∧ (α j).IsLat N'S ΛS ∧ (β j).IsLat N₁T ΛT ∧ (β j).IsLat N'T ΛT` using `fun j hj => ⟨A'S j, A'T j, by simpa only [BS, if_pos hj] using hlatS j, (hA j).2.1, by simpa only [BT, if_pos hj] using hlatT j, (hA j).2.2.2⟩`. Establish `hgv : ∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g` using `fun j hj => by`. Take `⟨ΛS, ΛT, a, b, c, d⟩` from `hsame j hj`. Establish `hji : (p j).v ≠ (p i).v` using `fun e => hil (by rw [← hinj e]; exact hj)`.

Establish `hk` using `(ValDbl.over_keep hstd hO₁).2 (p j).v hji (IH.1 j hj)`. Conclude with `(cc hstd (hunit j) hN₁S hN₁T h3 h4 a b c d hk).1`. Use `haveI := (hL i).1`. Use `haveI := (hL i).2.2.1`. Establish `hsp` using `sp1 hstd (hunit i) hN₁S hN₁T h3 h4 hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2 C.1 hO₁`.

Use `⟨fun j hj => ?_, fun Ψ f' => ?_⟩` and prove the remaining obligations. Break down `List.mem_cons.1 hj with rfl | hj'` into its components or cases. Conclude with `hsp.1`. Conclude with `hgv j hj'`. Rewrite using `[← front hstd hunit hinj hN₁S hN₁T h3 h4 i l hnd hil hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2 hsame C.1 IH.1 hgv hO₁ f']`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨m, hm, hmO⟩` from `ValDbl.overAll_cons.1 h`. Conclude with `ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).1 hm, (cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hmO.2.2.1).2 _ _ hmO⟩`. Introduce `h`.

Take `⟨m, hm, hmO⟩` from `ValDbl.overAll_cons.1 h`. Conclude with `ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).2 hm, (cc hstd (hunit i) hN₁S hN₁T h1 h2 hN₁Si (hA i).1 hN₁Ti (hA i).2.2.1 hmO.2.2.1).2 _ _ hmO⟩`.
-/
theorem gen (hstd : IsStdChar D ψ (-1)) {I : List ι} {P : Pl D → Prop} (hPl : Places p I P) (l : List ι) :
    l.Nodup → ∀ (NS N'S : Lat S) (NT N'T : Lat T) (AS A'S : ι → Submodule 𝒪[k] (n' → k))
      (AT A'T : ι → Submodule 𝒪[k] (n → k)),
    IsSelfDualC S NS → IsSelfDualC T NT → IsSelfDualC S N'S → IsSelfDualC T N'T →
    (∀ j, (AS j).IsLattice k ∧ (A'S j).IsLattice k ∧ (AT j).IsLattice k ∧ (A'T j).IsLattice k) →
    (∀ j, (α j).IsLat NS (AS j) ∧ (α j).IsLat N'S (A'S j) ∧ (β j).IsLat NT (AT j) ∧ (β j).IsLat N'T (A'T j)) →
    (∀ j, j ∉ l → A'S j = AS j ∧ A'T j = AT j) →
    ∀ f g, (∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) f) →
      OverAll ψ α β NS NT (fun j => latInd (A'S j) (A'T j)) l f g →
      (∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g) ∧
        ∀ Ψ f', OverAll ψ α β NS NT Ψ l f f' ↔ OverAll ψ α β N'S N'T Ψ l g f' := by
  have hunit := hPl.unit
  have hinj := hPl.inj
  induction l with
  | nil =>
    intro _ NS N'S NT N'T AS A'S AT A'T _ _ _ _ _ _ _ f g _ hg
    rw [ValDbl.overAll_nil.1 hg]
    exact ⟨fun j hj => by simp at hj, fun Ψ f' => Iff.rfl⟩
  | cons i l ih =>
    intro hl NS N'S NT N'T AS A'S AT A'T h1 h2 h3 h4 hL hA hout f g hf hg
    rw [List.nodup_cons] at hl
    obtain ⟨hil, hnd⟩ := hl
    let BS : ι → Submodule 𝒪[k] (n' → k) := fun j => if j ∈ l then A'S j else AS j
    let BT : ι → Submodule 𝒪[k] (n → k) := fun j => if j ∈ l then A'T j else AT j
    have hBS : ∀ j, (BS j).IsLattice k := fun j => by
      by_cases hj : j ∈ l
      · simp only [BS, if_pos hj]; exact (hL j).2.1
      · simp only [BS, if_neg hj]; exact (hL j).1
    have hBT : ∀ j, (BT j).IsLattice k := fun j => by
      by_cases hj : j ∈ l
      · simp only [BT, if_pos hj]; exact (hL j).2.2.2
      · simp only [BT, if_neg hj]; exact (hL j).2.2.1
    obtain ⟨N₁S, hN₁S, hlatS, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n' S α NS h1 BS hBS
    obtain ⟨N₁T, hN₁T, hlatT, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n T β NT h2 BT hBT
    obtain ⟨g₁, hg₁, hO⟩ := ValDbl.overAll_cons.1 hg
    have hg₁' : OverAll ψ α β NS NT (fun j => latInd (BS j) (BT j)) l f g₁ :=
      overAll_congrΨ l (fun j hj => by simp only [BS, BT, if_pos hj]) f g₁ hg₁
    have IH := ih hnd NS N₁S NT N₁T AS BS AT BT h1 h2 hN₁S hN₁T
      (fun j => ⟨(hL j).1, hBS j, (hL j).2.2.1, hBT j⟩) (fun j => ⟨(hA j).1, hlatS j, (hA j).2.2.1, hlatT j⟩)
      (fun j hj => ⟨by simp only [BS, if_neg hj], by simp only [BT, if_neg hj]⟩)
      f g₁ (fun j hj => hf j (List.mem_cons_of_mem _ hj)) hg₁'
    have hBi : BS i = AS i ∧ BT i = AT i := ⟨by simp only [BS, if_neg hil], by simp only [BT, if_neg hil]⟩
    have hN₁Si : (α i).IsLat N₁S (AS i) := hBi.1 ▸ hlatS i
    have hN₁Ti : (β i).IsLat N₁T (AT i) := hBi.2 ▸ hlatT i
    have hg₁v : Vac ψ S T NS NT (· = (p i).v) g₁ :=
      ValDbl.overAll_vac hstd hinj l f g₁ hg₁ i hil (hf i List.mem_cons_self)
    have C := cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hg₁v
    have hO₁ := C.2 _ _ hO
    have hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
        (α j).IsLat N₁S ΛS ∧ (α j).IsLat N'S ΛS ∧ (β j).IsLat N₁T ΛT ∧ (β j).IsLat N'T ΛT := fun j hj =>
      ⟨A'S j, A'T j, by simpa only [BS, if_pos hj] using hlatS j, (hA j).2.1,
        by simpa only [BT, if_pos hj] using hlatT j, (hA j).2.2.2⟩
    have hgv : ∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g := fun j hj => by
      obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame j hj
      have hji : (p j).v ≠ (p i).v := fun e => hil (by rw [← hinj e]; exact hj)
      have hk := (ValDbl.over_keep hstd hO₁).2 (p j).v hji (IH.1 j hj)
      exact (cc hstd (hunit j) hN₁S hN₁T h3 h4 a b c d hk).1
    haveI := (hL i).1
    haveI := (hL i).2.2.1
    have hsp := sp1 hstd (hunit i) hN₁S hN₁T h3 h4 hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2 C.1 hO₁
    refine ⟨fun j hj => ?_, fun Ψ f' => ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj'
      · exact hsp.1
      · exact hgv j hj'
    · rw [← front hstd hunit hinj hN₁S hN₁T h3 h4 i l hnd hil hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2
        hsame C.1 IH.1 hgv hO₁ f']
      constructor
      · intro h
        obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 h
        exact ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).1 hm,
          (cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hmO.2.2.1).2 _ _ hmO⟩
      · intro h
        obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 h
        exact ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).2 hm,
          (cc hstd (hunit i) hN₁S hN₁T h1 h2 hN₁Si (hA i).1 hN₁Ti (hA i).2.2.1 hmO.2.2.1).2 _ _ hmO⟩

end Gen

/- English proof (translation)
Introduce `D`. Unfold `RebaseAll`. Introduce `k _ _ _ _ ι p I P hPl n n' _ _ _ _ ψ hstd S T α β LS MS LT MT hLS hLT hMS hMT`. Use `choose ALS hALS1 hALS2 _hALS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 LS hLS`. Use `choose AMS hAMS1 hAMS2 _hAMS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 MS hMS`.

Use `choose ALT hALT1 hALT2 _hALT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 LT hLT`. Use `choose AMT hAMT1 hAMT2 _hAMT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 MT hMT`. Establish `hL : ∀ j, (ALS j).IsLattice k ∧ (AMS j).IsLattice k ∧ (ALT j).IsLattice k ∧ (AMT j).IsLattice k` using `fun j => ⟨hALS1 j, hAMS1 j, hALT1 j, hAMT1 j⟩`. Establish `hA : ∀ j, (α j).IsLat LS (ALS j) ∧ (α j).IsLat MS (AMS j) ∧ (β j).IsLat LT (ALT j) ∧ (β j).IsLat MT (AMT j)` using `fun j => ⟨hALS2 j, hAMS2 j, hALT2 j, hAMT2 j⟩`. Take `⟨e, he1, he2⟩` from `(GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β LS LT hLS hLT (fun i => latInd (AMS i) (AMT i))).1 (fun i => by haveI := hAMS1 i; haveI := hAMT1 i; exact latInd_mem_SB _ _)`.

Establish `AC'` using `GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β MS MT hMS hMT (fun i => latInd (ALS i) (ALT i))`. Take `⟨e', he'1, he'2⟩` from `AC'.1 (fun i => by haveI := hALS1 i; haveI := hALT1 i; exact latInd_mem_SB _ _)`. Use `⟨e, e', he1, he'1, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hfv : ∀ j, Vac ψ S T LS LT (· = (p j).v) f` using `fun j => ValDbl.vac_at ((hPl.mem _).2 ⟨j, rfl⟩) hf`. Take `⟨hgv, hiff⟩` from `gen hstd hPl I hPl.nodup LS MS LT MT ALS AMS ALT AMT hLS hLT hMS hMT hL hA (fun j hj => absurd (hPl.all j) hj) f (comb ψ S T e f) (fun j _ => hfv j) (he2 f hf)`.

Establish `hth : IsThetaFunO ψ S T (comb ψ S T e f)` using `ValDbl.overAll_theta hstd I f _ (he2 f hf) hf.1`. Establish `hgV : Vac ψ S T MS MT P (comb ψ S T e f)` using `⟨hth, GlobalTheory.VacLoc.latVac_of_places ψ S T MS MT P _ hth fun v hv => by obtain ⟨j, rfl⟩ := (hPl.mem v).1 hv; exact hgv j (hPl.all j)⟩`. Use `⟨hgV, ?_, hiff⟩` and prove the remaining obligations. Establish `hs` using `(hiff _ f).1 (overAll_self hstd hPl.unit hLS hLT (fun j => ⟨(hA j).1, (hA j).2.2.1⟩) f I fun j _ => hfv j)`. Conclude with `AC'.2.1 _ _ _ (he'2 _ hgV) hs`.
-/
theorem rebaseAll : ∀ D : D7, RebaseAll D := by
  intro D
  unfold RebaseAll
  intro k _ _ _ _ ι p I P hPl n n' _ _ _ _ ψ hstd S T α β LS MS LT MT hLS hLT hMS hMT
  choose ALS hALS1 hALS2 _hALS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 LS hLS
  choose AMS hAMS1 hAMS2 _hAMS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 MS hMS
  choose ALT hALT1 hALT2 _hALT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 LT hLT
  choose AMT hAMT1 hAMT2 _hAMT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 MT hMT
  have hL : ∀ j, (ALS j).IsLattice k ∧ (AMS j).IsLattice k ∧ (ALT j).IsLattice k ∧ (AMT j).IsLattice k :=
    fun j => ⟨hALS1 j, hAMS1 j, hALT1 j, hAMT1 j⟩
  have hA : ∀ j, (α j).IsLat LS (ALS j) ∧ (α j).IsLat MS (AMS j) ∧ (β j).IsLat LT (ALT j) ∧ (β j).IsLat MT (AMT j) :=
    fun j => ⟨hALS2 j, hAMS2 j, hALT2 j, hAMT2 j⟩
  obtain ⟨e, he1, he2⟩ := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β LS LT hLS hLT
    (fun i => latInd (AMS i) (AMT i))).1 (fun i => by haveI := hAMS1 i; haveI := hAMT1 i; exact latInd_mem_SB _ _)
  have AC' := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β MS MT hMS hMT (fun i => latInd (ALS i) (ALT i))
  obtain ⟨e', he'1, he'2⟩ := AC'.1 (fun i => by haveI := hALS1 i; haveI := hALT1 i; exact latInd_mem_SB _ _)
  refine ⟨e, e', he1, he'1, fun f hf => ?_⟩
  have hfv : ∀ j, Vac ψ S T LS LT (· = (p j).v) f := fun j => ValDbl.vac_at ((hPl.mem _).2 ⟨j, rfl⟩) hf
  obtain ⟨hgv, hiff⟩ := gen hstd hPl I hPl.nodup LS MS LT MT ALS AMS ALT AMT hLS hLT hMS hMT hL hA
    (fun j hj => absurd (hPl.all j) hj) f (comb ψ S T e f) (fun j _ => hfv j) (he2 f hf)
  have hth : IsThetaFunO ψ S T (comb ψ S T e f) := ValDbl.overAll_theta hstd I f _ (he2 f hf) hf.1
  have hgV : Vac ψ S T MS MT P (comb ψ S T e f) := ⟨hth, GlobalTheory.VacLoc.latVac_of_places ψ S T MS MT P _ hth
    fun v hv => by obtain ⟨j, rfl⟩ := (hPl.mem v).1 hv; exact hgv j (hPl.all j)⟩
  refine ⟨hgV, ?_, hiff⟩
  have hs := (hiff _ f).1 (overAll_self hstd hPl.unit hLS hLT (fun j => ⟨(hA j).1, (hA j).2.2.1⟩) f I
    fun j _ => hfv j)
  exact AC'.2.1 _ _ _ (he'2 _ hgV) hs

end GlobalTheory.FinPl.RebaseProof
