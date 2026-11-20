import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Detection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OmDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadicAlt

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `z hz hT` and use `h z hz fun σ hσ => hT σ (hST hσ)`.
-/
private theorem detects_mono {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    {S T : Set F.G₀} (hST : S ⊆ T) (h : Detects k S) : Detects k T :=
  fun z hz hT => h z hz fun σ hσ => hT σ (hST hσ)

/- English proof (translation)
Introduce `l _ F n h x hl hphi hε hN3`. Use `set S : Set F.G₀ := {σ | σ ∈ F.G' ∧ ∀ i : Fin (h + 1), (Polynomial.map (algebraMap (x i).A (FractionRing (x i).A)) ((mat (x i).ρ) σ).charpoly).Separable} with hS`. Establish `hcl : (F.G' : Set F.G₀) ⊆ closure S` using `Det.omDense x hN3`. Establish `hSG : S ⊆ F.G'` using `fun σ hσ => hσ.1`. Establish `k0 : ∀ i, Kap (x i)` using `fun i => (Det.kapEx (x i) hphi).some`.

Establish `hdet : ∀ i, Detects (k0 i) S` using `fun i => detection l F n (x i) (k0 i) hl hε S hSG hcl`. Use `choose Tf hTS hTd using fun i => Det.detFin (k0 i) S hphi (hdet i)`. Use `set U : Finset F.G₀ := Finset.univ.biUnion Tf with hU`. Set `sg : Fin U.card → F.G₀` to `fun a => (U.equivFin.symm a : F.G₀)`. Establish `hsgU : ∀ a, sg a ∈ U` using `fun a => (U.equivFin.symm a).2`.

Establish `hsgS : ∀ a, sg a ∈ S` using `fun a => by`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 (hsgU a)`. Conclude with `hTS i hi`. Establish `hTr : ∀ i, (Tf i : Set F.G₀) ⊆ Set.range sg` using `fun i y hy => by`. Establish `hyU : y ∈ U` using `Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩`.

Conclude with `⟨U.equivFin ⟨y, hyU⟩, by simp [sg]⟩`. Establish `hdr : ∀ i, Detects (k0 i) (Set.range sg)` using `fun i => detects_mono (k0 i) (hTr i) (hTd i)`. Use `choose d hd0 hd using fun i => Det.onePt (k0 i) sg (fun a => (hsgS a).2 i) (hdr i)`. Establish `hD0 : (∏ i, d i) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)`. Use `choose x' j k' al hext hcard hdet' hal using fun i => hd i (∏ i, d i) (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) hD0`.

Conclude with `⟨U.card, sg, x', j, k', al, fun a => (hsgS a).1, hext, fun i => by rw [hcard, hcard], hdet', fun i a => hal i a⟩`.
-/
theorem UpperTheory.V.Pa.choice :
    UpperTheory.V.Pa.Choice := by
  intro l _ F n h x hl hphi hε hN3
  classical
  set S : Set F.G₀ := {σ | σ ∈ F.G' ∧ ∀ i : Fin (h + 1),
    (Polynomial.map (algebraMap (x i).A (FractionRing (x i).A)) ((mat (x i).ρ) σ).charpoly).Separable} with hS
  have hcl : (F.G' : Set F.G₀) ⊆ closure S := Det.omDense x hN3
  have hSG : S ⊆ F.G' := fun σ hσ => hσ.1
  have k0 : ∀ i, Kap (x i) := fun i => (Det.kapEx (x i) hphi).some
  have hdet : ∀ i, Detects (k0 i) S := fun i => detection l F n (x i) (k0 i) hl hε S hSG hcl
  choose Tf hTS hTd using fun i => Det.detFin (k0 i) S hphi (hdet i)
  set U : Finset F.G₀ := Finset.univ.biUnion Tf with hU
  let sg : Fin U.card → F.G₀ := fun a => (U.equivFin.symm a : F.G₀)
  have hsgU : ∀ a, sg a ∈ U := fun a => (U.equivFin.symm a).2
  have hsgS : ∀ a, sg a ∈ S := fun a => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (hsgU a)
    exact hTS i hi
  have hTr : ∀ i, (Tf i : Set F.G₀) ⊆ Set.range sg := fun i y hy => by
    have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩
    exact ⟨U.equivFin ⟨y, hyU⟩, by simp [sg]⟩
  have hdr : ∀ i, Detects (k0 i) (Set.range sg) := fun i => detects_mono (k0 i) (hTr i) (hTd i)
  choose d hd0 hd using fun i => Det.onePt (k0 i) sg (fun a => (hsgS a).2 i) (hdr i)
  have hD0 : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
  choose x' j k' al hext hcard hdet' hal using
    fun i => hd i (∏ i, d i) (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) hD0
  exact ⟨U.card, sg, x', j, k', al, fun a => (hsgS a).1, hext, fun i => by rw [hcard, hcard],
    hdet', fun i a => hal i a⟩
