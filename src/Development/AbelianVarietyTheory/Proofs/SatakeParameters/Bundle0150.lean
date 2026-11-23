module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ}

def AwayAt (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)) (B : ℕ) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Φ x) ≤ 1) ∧ ∀ x z, z ∈ homAt {P} N N' → Φ (x + ((qOf P : E) ^ B) • z) = Φ x


open Classical in
def DatumAt (Sg S : Finset (HeightOneSpectrum (𝓞 E))) (g c : ℕ) (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Ξ x) ≤ 1) ∧ (∀ x, Ξ x ≠ 0 → x ∈ homAt Sg N N') ∧
    ∀ x z, z ∈ mulLat g (homAt Sg N N') → z ∈ mulLat c (homAt (S \ Sg) N N') → Ξ (x + z) = Ξ x

end Notions

def JetLossAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def LevelPrimes : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel →
    ∀ P : rowSG Pr sel mu, DegOneUnram P.1 ∧ (P.1 ∉ Pr.vGs → qOf P.1 ∉ S)

def HeckeUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : X.Tau → ℚ) (j : Fin m)
    (χ : Formalism.L2.Host.HChar X.E), X.Ok → Pr.Ok → IsMu0 Ch σ₀ e j χ →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)), p.Prime → (p : 𝓞 X.K) ∈ w.asIdeal →
      (p : 𝓞 X.E) ∉ P.asIdeal → ∀ (x : X.Eˣ) (k : X.K), σ₀ k = ((χ.locK P x : ℂˣ) : ℂ) → w.valuation X.K k = 1

def TwistUnit : Prop :=
  ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] [NumberField K] (S : Set ℕ)
    (mu : Tup F E K S) (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.valuation K ((unifVal (mu : Chr F E K) P : Kˣ) : K) = 1 ∧ w.valuation K ((qValC (mu : Chr F E K) P : Kˣ) : K) = 1

def ScalarUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (e : Fin R.m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → Ch.Tied G.σ₀ e G.mu0 eta → L.Ok Ch sel mu cst G m2 →
    ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ j, j < R.m →
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1) ∧
      ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
        IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
        w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1

def EntryAtG : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      DegOneUnram P.1 → FnMod P.1 (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))

def VolumeAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j)
    (w : HeightOneSpectrum (𝓞 X.K)), P ∉ Pr.vGs → DegOneUnram P → ((qOf P : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
    w.valuation X.K (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) sharp j P) h)
      (Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)))⁻¹ ≤ 1

def EntryAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal → (∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1) →
      (∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))) ∧
      ∀ (al : L.β m2) (y : Sp X.E (R.N (m2 + 1))),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) fun x => PsiAt Ch sel mu cst m2 P (L.h m2 al P) x y

def TopAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word), Pr.Ok → IsSel X sel → Pr.T u ∈ S →
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
      ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
        AwayAt P.1 w cst.B p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P)

def JetOpIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ HAt w lam M, c • jetOp lam lam' J n F ∈ HAt w lam' MW

def NabLeDel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (∀ τ, (lam τ).spread < p) →
      localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M)

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.ColPeriod.N_lt_succ (R : _root_.Formalism.BasicNotions.Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold _root_.Formalism.BasicNotions.Ranks.N
  simp

def ChainWeights : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (j : ℕ), j < R.m →
    ∃ s s' : X.Tau → ℤ, WtCompat (N_lt_succ R j) (W.lamTrue u j) (W.lamTrue u (j + 1)) s s' (nuLast W u j) ∧
      ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a

def PartitionSize : Prop :=
  ∀ (D : D7) (EX : ErrX D) (u : D.what₂.Word) (j : ℕ), j < D.R.m → ∀ τ : D.what₂.Tau,
    nuAbs D u (j + 1) τ = ((∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ)

def StdMove : Prop :=
  ∀ (X : Fields) (Pr : Primes X), Pr.Ok → ∀ (i : Fin 2) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N →
    ∃ γ : UF X.E n, StdOver (Pr.g i) (gmap γ.1 N)

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairingEquivContra
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvPairing

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) :
    π'.IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun b => ⟨B.flip b, mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hπ' b).mem_nhds (by simp)) fun g hg => by
          have hg' : π' g b = b := hg
          ext a
          show B (π g⁻¹ a) b = B a b
          have h := hB g (π g⁻¹ a) b
          rw [hg'] at h
          rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])⟩
      map_add' := fun b c => Subtype.ext (by simp)
      map_smul' := fun c b => Subtype.ext (by simp) }
  isIntertwining' g := by
    refine LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun a => ?_)
    show B a (π' g b) = B (π g⁻¹ a) b
    have h := hB g (π g⁻¹ a) b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem pairMap_apply (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (a : V) (b : W) :
    ((pairMap π hπ' B hB b : smoothPart π.dual) : Module.Dual ℂ V) a = B a b := rfl

theorem eq_zero_of_pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b)
    (h : ∀ b, pairMap π hπ' B hB b = 0) : B = 0 :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) a) (h b)
    simpa [pairMap_apply] using this

theorem pairMap_bijective (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (hB0 : B ≠ 0)
    (hirr' : π'.IsIrreducible) (hirr : (contra π).IsIrreducible) :
    Function.Bijective (pairMap π hπ' B hB) := by
  set f := pairMap π hπ' B hB with hf
  constructor
  · let S : Subrepresentation π' :=
      { toSubmodule := LinearMap.ker f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [LinearMap.mem_ker] at hv ⊢
          have := LinearMap.congr_fun (f.isIntertwining' g) v
          simp only [LinearMap.comp_apply] at this
          rw [this, hv, map_zero] }
    rcases hirr'.eq_bot_or_eq_top S with hS | hS
    · intro x y hxy
      have : x - y ∈ S.toSubmodule := by
        show f.toLinearMap (x - y) = 0
        rw [map_sub]; exact sub_eq_zero.2 hxy
      rw [hS] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 this)
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : b ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      exact this
  · let R : Subrepresentation (contra π) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨π' g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩

end GlobalTheory.InvPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_lpDim_mono0_charPol : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L]
    [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (x : WD h) (x' : WD h'), Restricts x x' →
    x'.lpDim = x.lpDim ∧ (x'.mono0 ↔ x.mono0) ∧ ∀ (σ : Weil h) (σ' : Weil h'),
      (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → x'.charPol σ' = x.charPol σ := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' x x' hr
  obtain ⟨n, a, b, rfl, rfl, hN, hρ⟩ := hr
  refine ⟨by rw [WD.lpDim_mk, WD.lpDim_mk], by rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN], fun σ σ' hs => ?_⟩
  rw [WD.charPol_mk, WD.charPol_mk, hρ σ σ' hs]

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeEqUnitaryMulIntegralGL
section
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem mem_GLint_of_entries' {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

def cTGL {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (a : GL (Fin n) L) : GL (Fin n) L :=
  ⟨Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L), Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one],
    by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]⟩

theorem selfDual_eq_unitary_mul_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  intro L _ _ _ ϖ σ q n JS hU _hq hJS hJh a ha
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have cTcT : ∀ M : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    intro M; ext i j; simp [Formalism.UG.cT, hσ]
  have hJc : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j; simp [Formalism.UG.cT, hJh]
  set G : GL (Fin n) L := cTGL σ a * JS * a with hGdef
  have hGv : (G : Matrix (Fin n) (Fin n) L) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := rfl
  have hGi : ((G⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hGdef, _root_.mul_inv_rev, _root_.mul_inv_rev, ← _root_.mul_assoc]; rfl
  have hGint : G ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) :=
    mem_GLint_of_entries' _ G (fun i j => by rw [hGv]; exact ha.1 i j) (fun i j => by rw [hGi]; exact ha.2 i j)
  have hGc : Formalism.UG.cT σ (G : Matrix (Fin n) (Fin n) L) = G := by
    rw [hGv, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTcT, hJc, Matrix.mul_assoc]
  have hGh : ∀ i j, σ ((G : Matrix (Fin n) (Fin n) L) i j) = (G : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    have := congrFun (congrFun hGc j) i
    simpa [Formalism.UG.cT] using this
  obtain ⟨P, hP, eP⟩ := GlobalTheory.NormalHyp.frame hU hGint hGh
  obtain ⟨Q, hQ, eQ⟩ := GlobalTheory.NormalHyp.frame hU hJS hJh
  have hU' : a * P * Q⁻¹ ∈ Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
      ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = JS
    have e1 : Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
    have e2 : (Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv Q
    rw [hGv] at eP
    calc Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
          ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (P : Matrix (Fin n) (Fin n) L) * (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) *
              (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (Q : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by rw [eP, eQ]
      _ = (Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L)) *
            (JS : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          simp only [Matrix.mul_assoc]
      _ = JS := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨a * P * Q⁻¹, hU'⟩, Q * P⁻¹, mul_mem hQ (inv_mem hP), ?_⟩
  show a = a * P * Q⁻¹ * (Q * P⁻¹)
  group

end GlobalTheory.Hk3.HoweG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentity
section
open Matrix

namespace GlobalTheory

theorem skewConj_cT_mul_and_trace :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  intro L _ _ σ hσ n r JS M Γ hJ hΓ
  have hmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L),
      Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
    intro a b c A B
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  have hJ' : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j
    simp [Formalism.UG.cT, hJ]
  have hΓ' : Formalism.UG.cT σ Γ = -Γ := by
    ext i j
    simp [Formalism.UG.cT, hΓ]
  refine ⟨?_, ?_⟩
  · rw [hmul, hmul, hmul, hcc, hJ', hΓ']
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  · intro n' JT y
    rw [hmul, Matrix.mul_assoc (M * Γ * Formalism.UG.cT σ M), Units.mul_inv, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm M]
    simp only [Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceSkewHermitianGramIntegral
section
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem trace_skewHermitian_gram_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ δ hv hδ n n' r JT a y M e Γ hJT hya haM hΓ
  have hmem : ∀ x : L, x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := fun _ => Iff.rfl
  set N := y * M with hNdef
  have hNe : N = (y * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) := by
    rw [hNdef, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L)]
    have : (a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mul]
  have hN : ∀ q k, N q k * ϖ ^ e k ∈ Formalism.UG.intL L := by
    intro q k
    rw [hNe, Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ (hya q i) (haM i k)
  have hNσ : ∀ p j, σ (N p j) * ϖ ^ e j ∈ Formalism.UG.intL L := by
    intro p j
    have h := hN p j
    rw [hmem] at h ⊢
    rw [map_mul, hv]; rw [map_mul] at h; exact h
  have hG : ∀ j k, (Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k * ϖ ^ (e j + e k) ∈ Formalism.UG.intL L := by
    intro j k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    refine Subring.sum_mem _ fun p _ => ?_
    have hc : Formalism.UG.cT σ N j p = σ (N p j) := rfl
    rw [hc, pow_add]
    have : σ (N p j) * (JT : Matrix (Fin n') (Fin n') L) p q * N q k * (ϖ ^ e j * ϖ ^ e k) =
        (σ (N p j) * ϖ ^ e j) * (JT : Matrix (Fin n') (Fin n') L) p q * (N q k * ϖ ^ e k) := by ring
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hNσ p j) (hJT p q)) (hN q k)
  refine Subring.mul_mem _ hδ ?_
  rw [Matrix.trace]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [hmem, map_mul]
  have h1 := hΓ.2 k j
  have h2 := hG j k
  rw [hmem, map_mul, map_pow] at h2
  calc Valued.v (Γ k j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k)
      ≤ Valued.v ϖ ^ (e k + e j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) :=
        mul_le_mul_of_nonneg_right h1 zero_le'
    _ = Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) * Valued.v ϖ ^ (e j + e k) := by
        rw [mul_comm, add_comm]
    _ ≤ 1 := h2

end GlobalTheory.Hk3.GramSep
end

