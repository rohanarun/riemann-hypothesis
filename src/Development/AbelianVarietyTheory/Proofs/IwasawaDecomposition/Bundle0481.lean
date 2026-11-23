module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataDeterminedByValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.DatExtForms

theorem decoSet_eq (B B' : Base) (h : B'.toPre = B.toPre) (X : PreX B.toPre) (X' : PreX B'.toPre) (hx : HEq X' X)
    (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (Q' : Finset (HeightOneSpectrum (𝓞 B'.fields.E))) (hQ : Q = ∅) (hQ' : Q' = ∅) :
    Formalism.L2.Col.DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := Formalism.L2.Col.uSG (B'.primes X').vGs Q') =
      Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := Formalism.L2.Col.uSG (B.primes X).vGs Q) := by
  subst hQ hQ'
  cases B
  cases B'
  dsimp only at h X X' hx ⊢
  subst h
  cases hx
  rfl


set_option maxHeartbeats 1000000 in
theorem forms_lift_eq_of_values : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX
            (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T'
            {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX'
            (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (f
            : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX
            (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr :=
            B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts
            w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map
            (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px)
            B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr :=
            B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I
            T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f)
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel
            (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
            ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch
            w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL
            : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res
            (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields)
            (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr
            := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts
            w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V)
            d).1)) → ∀ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px)
            B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)), (∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F
            (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d
            : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d'
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel
            (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
            ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch
            w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL
            : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)
            : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD
            (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f, (Formalism.L2.Col.GSD.res
            (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j'
            : ℕ) + 1))).symm (L f) = b.lift ((Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr
            := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm
            f)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w hE hf hP hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ L hL b hb f0
  have hD : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D = (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D :=
    decoSet_eq B B' hE.1 w.px w'.px hpx _ _ (by exact Formalism.L2.DIV.twistPrimes_trivialTuple_empty w.I.sel) (by exact Formalism.L2.DIV.twistPrimes_trivialTuple_empty w'.I.sel)
  have key : ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (x : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun), (∀ (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d →
      HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((x : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1))
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1))) → x = b.lift ψ := by
    intro ψ x hx
    apply Subtype.ext
    funext d'
    have hdd : HEq d' (cast hD d') := (cast_heq hD d').symm
    have h3 := eq_of_heq ((hx _ _ hdd).trans (hb ψ _ _ hdd).symm)
    exact Subtype.ext (MvPolynomial.map_injective _ (RingHom.injective _) h3)
  exact key _ _ (hL f0)

end GlobalTheory.DatExtForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC


open _root_.Formalism.L2.Col in
theorem repCSD_lift_of_reading {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
    (S : GSD K) (S' : GSD K') (hS : S.Ok) (hS' : S'.Ok) {A A' : Type} [Group A] [Group A']
    (ρ : Representation K A S.EqFun) (ρ' : Representation K' A' S'.EqFun) {T T' : Type} (rd : S.V → T) (rd' : S'.V → T')
    (hrd' : Function.Injective rd') (L : (S.toCSD hS).Forms → (S'.toCSD hS').Forms)
    (hC : ∀ (f : (S.toCSD hS).Forms) (d : S.D) (d' : S'.D), HEq d' d →
      HEq (rd' ((((S'.res hS').symm (L f) : S'.EqFun) : S'.D → S'.V) d')) (rd ((((S.res hS).symm f : S.EqFun) : S.D → S.V) d)))
    (hex : ∀ d' : S'.D, ∃ d : S.D, HEq d' d) (a : A) (a' : A') (t : S.D → S.D) (t' : S'.D → S'.D)
    (hρ : ∀ (φ : S.EqFun) d, (ρ a φ : S.D → S.V) d = (φ : S.D → S.V) (t d))
    (hρ' : ∀ (φ : S'.EqFun) d, (ρ' a' φ : S'.D → S'.V) d = (φ : S'.D → S'.V) (t' d))
    (ht : ∀ (d : S.D) (d' : S'.D), HEq d' d → HEq (t' d') (t d)) (f : (S.toCSD hS).Forms) :
    S'.repCSD hS' ρ' a' (L f) = L (S.repCSD hS ρ a f) := by
  apply (S'.res hS').symm.injective
  apply Subtype.ext
  funext d'
  apply hrd'
  obtain ⟨d, hd⟩ := hex d'
  have e1 : (S'.res hS').symm (S'.repCSD hS' ρ' a' (L f)) = ρ' a' ((S'.res hS').symm (L f)) := by
    simp [GSD.repCSD]
  have e2 : (S.res hS).symm (S.repCSD hS ρ a f) = ρ a ((S.res hS).symm f) := by
    simp [GSD.repCSD]
  rw [e1, hρ']
  have h1 := hC f (t d) (t' d') (ht d d' hd)
  have h2 := hC (S.repCSD hS ρ a f) d d' hd
  rw [e2, hρ] at h2
  exact eq_of_heq (h1.trans h2.symm)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_primes {X : Fields} {n r : ℕ} (h : r ≤ n) {SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : Q' = Q) :
    (∀ d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q'), ∃ d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q), HEq d' d) ∧
    ∀ (g : G0 X.E SG r) (d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q)) (d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q')), HEq d' d →
      HEq (((1 : UF X.E n), (extGLG Q' (diagonalEmbeddingProduct SG h g))⁻¹) • d') (((1 : UF X.E n), (extGLG Q (diagonalEmbeddingProduct SG h g))⁻¹) • d) := by
  subst hQ
  exact ⟨fun d' => ⟨d', HEq.rfl⟩, fun g d d' hd => by cases hd; rfl⟩


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E))
    (sel' : HeightOneSpectrum (𝓞 B'.fields.F) → HeightOneSpectrum (𝓞 B'.fields.E)) {S S' : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K S) (mu' : Tup B'.fields.F B'.fields.E B'.fields.K S')
    (hQ : QE sel (mu : Chr B.fields.F B.fields.E B.fields.K) = ∅)
    (hQ' : QE sel' (mu' : Chr B'.fields.F B'.fields.E B'.fields.K) = ∅) :
    (∀ d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu'),
      ∃ d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu), HEq d' d) ∧
    ∀ (g : Gc B px) (g' : Gc B' px'), HEq g' g → ∀ (d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu))
      (d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu')), HEq d' d →
      HEq (((1 : UF B'.fields.E B'.R.nV), (unipotentGroupBlockEmbedding (B'.primes px') sel' mu' (r_le_nV B'.R) g')⁻¹) • d')
        (((1 : UF B.fields.E B.R.nV), (unipotentGroupBlockEmbedding (B.primes px) sel mu (r_le_nV B.R) g)⁻¹) • d) := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  refine ⟨fun d' => (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).1 d', fun g g' hg d d' hd => ?_⟩
  have e := eq_of_heq hg
  subst e
  exact (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).2 _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC

set_option maxHeartbeats 8000000 in
theorem GlobalTheory.Mem.R3.DefLatBC.act_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ _ e he L _ hC g f0 => ?_
  have hP := GlobalTheory.Mem.R3.DefLatBC.decoratedLattice_translates_heq_of_eq_preData B B' w.px w'.px hE.1 hp w.I.sel w'.I.sel
    (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
    (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _) (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _)
  have hinj : Function.Injective fun v : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V => MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) v.1 :=
    (MvPolynomial.map_injective _ (B'.embLL : B'.fields.K →+* ℂ).injective).comp Subtype.val_injective
  exact GlobalTheory.Mem.R3.DefLatBC.repCSD_lift_of_reading (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1))
    (fun v => MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) v.1) _ hinj (fun x => L x) hC hP.1 g (e g) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun d d' hd => hP.2 g (e g) (he g) d d' hd) f0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

section GoodTransport

open Formalism.L2.DIV

theorem absIrr_one_ne_zero {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) : χ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  intro h0
  have h1 : ρ.character 1 = (n : AlgebraicClosure K) := by
    rw [Representation.char_one]; simp
  rw [hχ, h0, map_zero] at h1
  have hn : n = 0 := by exact_mod_cast h1.symm
  subst hn
  obtain ⟨a, b, hab⟩ := hρ.toNontrivial.exists_pair_ne
  apply hab
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

theorem eq_of_idemOf_eq {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {X Y : Finset (G → K)}
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (hYX : Y ⊆ X) (h : idemOf Y = idemOf X) : X = Y := by
  classical
  by_contra hne
  obtain ⟨χ, hχX, hχY⟩ : ∃ χ ∈ X, χ ∉ Y := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.Subset.antisymm hc hYX)
  have hsplit : idemOf (X \ Y) + idemOf Y = idemOf X := by
    unfold idemOf
    exact Finset.sum_sdiff hYX
  have h0 : idemOf (X \ Y) = 0 := by
    rw [h] at hsplit
    simpa using hsplit
  have hmem : χ ∈ X \ Y := Finset.mem_sdiff.2 ⟨hχX, hχY⟩
  have hprod : chiIdem χ * idemOf (X \ Y) = chiIdem χ := by
    unfold idemOf
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun χ' hχ' =>
      chiIdem_mul (hX χ hχX) (hX χ' (Finset.mem_sdiff.1 hχ').1)]
    rw [Finset.sum_ite_eq, if_pos hmem]
  rw [h0, mul_zero] at hprod
  have hc := congrArg (fun a : MonoidAlgebra K G => a.coeff 1) hprod
  simp only [coeff_chiIdem, inv_one] at hc
  have hne1 := absIrr_one_ne_zero (hX χ hχX)
  have hcard : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : χ 1 / (Fintype.card G : K) * χ 1 ≠ 0 := mul_ne_zero (div_ne_zero hne1 hcard) hne1
  exact this (by simpa using hc.symm)

theorem good_transport {K K' G G' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    [Group G'] [Fintype G'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (φ : K →+* K') (hφ : ∀ x, σ' (φ x) = σ x) (e : G ≃* G')
    (c : G → ℂ) (c' : G' → ℂ) (hc : ∀ g, c' (e g) = c g) (X : Finset (G → K)) (X' : Finset (G' → K'))
    (hX : ∀ χ, χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, c g * σ (χ g) = σ (χ 1)) (hX2 : ∀ g, σ ((idemOf X).coeff g) = c g)
    (hX' : ∀ χ, χ ∈ X' ↔ IsAbsIrrChar χ ∧ ∑ g, c' g * σ' (χ g) = σ' (χ 1)) (hX2' : ∀ g, σ' ((idemOf X').coeff g) = c' g)
    (χ' : G' → K') : χ' ∈ X' ↔ ∃ χ ∈ X, χ' = fun g => φ (χ (e.symm g)) := by
  classical
  have sup : ∀ χ ∈ X, (fun g => φ (χ (e.symm g))) ∈ X' := by
    intro χ hχ
    obtain ⟨hirr, hsum⟩ := (hX χ).1 hχ
    refine (hX' _).2 ⟨isAbsIrrChar_comp e.symm (_root_.GlobalTheory.AbsIrrMap.isAbsIrrChar_map φ χ hirr), ?_⟩
    rw [← Equiv.sum_comp e.toEquiv]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply, hc, hφ, map_one]
    exact hsum
  refine ⟨fun hχ' => ?_, fun ⟨χ, hχ, he⟩ => he ▸ sup χ hχ⟩
  set F : (G → K) → (G' → K') := fun χ g => φ (χ (e.symm g)) with hF
  have hinj : Function.Injective F := by
    intro χ₁ χ₂ h12
    funext g
    have := congrFun h12 (e g)
    simp only [hF, MulEquiv.symm_apply_apply] at this
    exact φ.injective this
  have hYX : X.image F ⊆ X' := by
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
    exact sup χ hχ
  have hcard : (Fintype.card G' : ℂ) = (Fintype.card G : ℂ) := by
    rw [Fintype.card_congr e.toEquiv]
  have hid : idemOf (X.image F) = idemOf X' := by
    apply MonoidAlgebra.ext
    ext t
    apply σ'.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX2', coeff_idemOf, Finset.sum_image fun a _ b _ h => hinj h, map_sum]
    have := hX2 (e.symm t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_idemOf, map_sum] at this
    rw [← hc (e.symm t), MulEquiv.apply_symm_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [hF, map_mul, map_div₀, map_natCast, hφ, map_one, map_inv, hcard]
  have := eq_of_idemOf_eq (fun ψ hψ => ((hX' ψ).1 hψ).1) hYX hid
  rw [this] at hχ'
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hχ'
  exact ⟨χ, hχ, rfl⟩

end GoodTransport

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC

theorem bc_eq_of_heq {X : Type} [Group X] {E : Type} [Field E] [NumberField E] {r m : ℕ} {P P' : Finset (Pl E)} (hP : P' = P)
    (a : X ≃* Formalism.L2.DIV.G0 P r) (a' : X ≃* Formalism.L2.DIV.G0 P' r) (h : HEq a' a) (g : X) (Q : P) (Q' : P')
    (hQ : (Q' : Pl E) = Q) (i : ZMod m ≃+* kP Q.1) (i' : ZMod m ≃+* kP Q'.1) (x x' : GL (Fin r) (ZMod m))
    (hx : a g Q = Formalism.UG.bc (i : ZMod m →+* kP Q.1) x) (hx' : a' g Q' = Formalism.UG.bc (i' : ZMod m →+* kP Q'.1) x') : x' = x := by
  subst hP
  cases h
  obtain ⟨Q, hQm⟩ := Q
  obtain ⟨Q', hQm'⟩ := Q'
  dsimp only at hQ
  subst hQ
  have hi : (i' : ZMod m →+* kP Q') = (i : ZMod m →+* kP Q') := Subsingleton.elim _ _
  rw [hi] at hx'
  have h2 : Formalism.UG.bc (i : ZMod m →+* kP Q') x' = Formalism.UG.bc (i : ZMod m →+* kP Q') x := hx'.symm.trans hx
  have hinj : Function.Injective (i : ZMod m →+* kP Q') := i.injective
  apply Units.ext
  apply Matrix.ext
  intro s t
  have := congrArg (fun y : GL (Fin r) (kP Q') => (y : Matrix (Fin r) (Fin r) (kP Q')) s t) h2
  exact hinj (by simpa [Formalism.UG.bc] using this)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


set_option maxHeartbeats 1000000 in
theorem goodIdempotents_agree_extendedData {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (hG : GrpTrue Z.N f) (hG' : GrpTrue Z'.N f')
    (hx : ExtN z z') (e : Gc B w.px ≃* Gc B' w'.px) (he : ∀ g, HEq (e g) g) (g : Gc B w.px) :
    (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) (e g)) =
      (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) := by
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  have heg : e g = g := eq_of_heq (he g)
  rw [heg]
  obtain ⟨plg, iso, hpl, -, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hpl', -, -, hbc'⟩ := z'.pins.keep.grp
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : z'.R.Pg = z.R.Pg := eq_of_heq hx.Pg
  have hQ : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact bc_eq_of_heq hP z.R.eG z'.R.eG hx.eG g _ _ hQ (iso ⟨k, v⟩) (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _
    (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.DefLatBC

theorem GlobalTheory.Mem.R3.DefLatBC.good_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ χ' : Gc B' w'.px → (w'.st Z').toD7.what₂.LL, χ' ∈ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).X ↔ ∃ χ ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).X, χ' = fun g => φ (χ (e.symm g))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z hG _ _ _ Z' hX' hG' _ _ z' _ hx j j' hj φ hφ e he χ' => ?_
  show χ' ∈ z'.Xg ↔ ∃ χ : Gc B w.px → (w.st Z).toD7.what₂.LL, χ ∈ z.Xg ∧ χ' = fun g => φ (χ (e.symm g))
  have g1 := (goodSet_iff _ _ _).1 z.good
  have g2 := (goodSet_iff _ _ _).1 z'.good
  exact GlobalTheory.Mem.R3.DefLatBC.good_transport (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL φ hφ e
    (fun g => (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g))
    (fun g => (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) g))
    (GlobalTheory.Mem.R3.DefLatBC.goodIdempotents_agree_extendedData z z' hE.1 hf hp hG hG' hx e he) z.Xg z'.Xg g1.1 g1.2 g2.1 g2.2 χ'
end

