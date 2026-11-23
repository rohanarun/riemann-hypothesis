module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}


omit [IsAlgClosure E Ω] in
def Weak (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ UpperTheory.V.Af.AttC ι r π

def IsWeight (π : CuspSub E a) (wt : ℤ) : Prop :=
  ∀ τ : E →+* ℂ, (CG.mk π).infChar (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
    ((CG.mk π).infChar τ).map fun z => (a : ℂ) - 1 - (wt : ℂ) - z

inductive Clause
  | ss | pure | dR | crys | iwa

def ClauseAt (c : Clause) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  match c with
  | .ss => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g
  | .pure => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
  | .iwa => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
        IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
          ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

def Good (l : ℕ) (π : CuspSub E a) : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat w B

inductive Level
  | all | good | csd

def InScope (s : Level) (l : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) : Prop :=
  (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π χ ∧
    match s with
    | .all => True
    | .good => Good l π
    | .csd => Good l π ∧ χ = quadChar E ^ a

def PlaceOK (s : Level) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  match s with
  | .all => True
  | _ => GlobalTheory.UnitaryBC.IsSplitAt w

def Ex (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∃ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r

def Holds (s : Level) (c : Clause) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ClauseAt c π ι r w

structure IsLift {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    (π : CuspSub K a) (P : CuspSub M a) : Prop where
  sat : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), normV w = normV (w.under (𝓞 K)) ^ f →
    (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))
  inf : ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))
  loc : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) (i : v.adicCompletion K ≃+* w.adicCompletion M),
    Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def QuadLift : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a,
    (∃ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 K)) B) →
    ∃ P : CuspSub M a, IsLift π P

theorem InScope.all {s : Level} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} (h : InScope s l π χ) : InScope .all l π χ :=
  ⟨h.1, h.2.1, trivial⟩

end GlobalTheory.GalCut

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem card_autU (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) = Nat.card (Mem.Col2.autO N) :=
  Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, γ.1.2, mem_autLat.2 (mem_autU.1 γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, mem_autU.2 (mem_autLat.1 γ.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_autU_dvd_tilN (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) ∣ Nat.card (autU (tilN N)) := by
  let f : autU N →* autU (tilN N) :=
    ((extUH rfl).comp (autU N).subtype).codRestrict _ fun γ => mem_autU.2 (by
      have h := tilN_gmap γ.1.1 N
      rw [mem_autU.1 γ.2] at h
      exact h.symm)
  refine Subgroup.card_dvd_of_injective f fun a b hab => Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  have h : extE a.1.1 = extE b.1.1 := congrArg (fun z : autU (tilN N) => z.1.1) hab
  have h1 := initL_extE a.1.1 (incl E n x)
  rw [h, initL_extE] at h1
  have h2 : initL E n (incl E n x) = x := by
    funext i
    simp [initL, incl, LinearMap.funLeft_apply]
  rw [h2] at h1
  exact h1.symm

theorem exists_card_autU_dvd {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (k : ℕ) :
    ∃ N' : Submodule (𝓞 E) (Sp E (n + k)), IsSdLat N' ∧ Nat.card (autU N) ∣ Nat.card (autU N') := by
  induction k with
  | zero => exact ⟨N, hN, dvd_rfl⟩
  | succ k ih =>
    obtain ⟨N', h1, h2⟩ := ih
    exact ⟨tilN N', ⟨tilN_lattice h1.1, tilN_unimodular h1.2⟩, h2.trans (card_autU_dvd_tilN N')⟩

theorem card_autU_dvd_DGam (hE : PosStar E) (R : Ranks) (hm : 1 ≤ R.m) {i : ℕ} (hi : i ≤ R.m) {N : Submodule (𝓞 E) (Sp E (R.N i))}
    (hN : IsSdLat N) : Nat.card (autU N) ∣ Mem.Col2.DGam E R := by
  have hle : R.N i ≤ R.N R.m := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨N', h1, h2⟩ := exists_card_autU_dvd hN k
  refine h2.trans ?_
  rw [card_autU]
  exact Mem.Col2.dvd_DGam hE R (hk ▸ Mem.Col2.N_mem_gamRanks R hm le_rfl) h1.1 h1.2

end Aut

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ)
  (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ)

def muInvPt (i : ℕ) {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) p.deco.1.N (frsF sel mu p)

def rhoPt (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) : ℂ :=
  σ (muInvPt Ch sel mu cst i p) * chi (R.N i) p.deco.1.N ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoPt' (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) : ℂ :=
  (σ (muInvPt Ch sel mu cst i p))⁻¹ * chi (R.N (i + 1)) p.deco.1.N ^ (((R.N i / 2 : ℕ) : ℤ))

def RhoUnit : Prop :=
  (∀ i, i < R.m → ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr)‖ = 1) ∧
  ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → ‖chi n N‖ = 1

def ChiSplit (A : Amb X) : Prop :=
  ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    A.chiF a b N N' = chi a N ^ (((b / 2 : ℕ) : ℤ)) * chi b N' ^ (-((a / 2 : ℕ) : ℤ))

variable {Ch sel mu cst σ chi}

theorem RhoUnit.norm_rhoPt (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) :
    ‖rhoPt Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt, norm_mul, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, one_mul]

theorem RhoUnit.norm_rhoPt' (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) :
    ‖rhoPt' Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt', norm_mul, norm_inv, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, inv_one, one_mul]

end Rho

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (P : LevFam X.E X.K R.r Pr.vGs) (c : TopDepth R cst.M)

@[reducible] def twFam : ℕ → GFam X.K := levFam W sel mu cst L u m2 b hY (topLevG Ch P) (topLevQ R sel mu c.pos)

def TwEquiv : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    TopEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P c

variable {W Ch sel mu cst L A u m2 b hY P c}

def twistedKernelPointCoset (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (al : L.β m2) :
    ClsKer ((chF W sel mu L u m2).mem al) (cplMem W sel mu cst L u m2 b hY).gsd :=
  cplKer1 (topCpl h.2.1 h.2.2 al)

def twistedKernelCosetPoint (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) :
    ClsKer (cplMem W sel mu cst L u m2 b hY).gsd (frmMem W sel mu L u (topLevG Ch P) (topLevQ R sel mu c.pos)).gsd where
  k d p' := topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) d.1.1 d.1.2 p'
  equiv g g₁ d p' := h.2.2 g g₁ d.1.1 d.1.2 p'

def twKer (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) : KerFam (twFam W Ch sel mu cst L u m2 b hY P c) :=
  spKer (matFam h.1) (twistedKernelPointCoset h) (twistedKernelCosetPoint h)

def twXi (i j : ℕ) (e : j = i + 1) : ∀ (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β),
    (twFam W Ch sel mu cst L u m2 b hY P c i).D β → (twFam W Ch sel mu cst L u m2 b hY P c j).D β' → HomE X.E (R.N i) (R.N j) → X.K
  | .mat al _, .mat be _ =>
    (match j, e, be with | _, rfl, be => XiEntry Ch sel mu cst L i al be :
      ChPt (R := R) sel mu u i → ChPt (R := R) sel mu u j → HomE X.E (R.N i) (R.N j) → X.K)
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : m2 = i), h', al with
      | _, _, rfl, rfl, al => fun p₀ d => XiCpl1 Ch sel mu cst L m2 al p₀ d.1.1 d.1.2 :
      ChPt (R := R) sel mu u i → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.cpl h') → HomE X.E (R.N i) (R.N j) → X.K)
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => fun d p' => XiTop Ch sel mu cst m2 d.1.1 d.1.2 p' :
      (twFam W Ch sel mu cst L u m2 b hY P c i).D (.cpl h) → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.top h') →
        HomE X.E (R.N i) (R.N j) → X.K)
  | .mat _ _, .top _ => fun _ _ _ => 0
  | .cpl _, .mat _ _ => fun _ _ _ => 0
  | .cpl _, .cpl _ => fun _ _ _ => 0
  | .top _, _ => fun _ _ _ => 0

def twRep (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : ChPt (R := R) sel mu u i :=
  levPt i x.1 (((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2)

def twSrc (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi) : ChSrc X R where
  F := twFam W Ch sel mu cst L u m2 b hY P c
  ok := levFam_ok hF (topGSD_ok W Ch sel mu hX P u c)
  lam := W.lamTrue u
  eV _ := LinearEquiv.refl _ _
  kk := twKer hK
  rho i x := rhoPt Ch sel mu cst A.σ₀ chi i (twRep i x)
  rho' i x := rhoPt' Ch sel mu cst A.σ₀ chi i (twRep (i + 1) x)
  rho_norm _ hi _ := hρ.norm_rhoPt hi _
  rho'_norm _ hi _ := hρ.norm_rhoPt' hi _
  DG := Mem.Col2.DGam X.E R
  DG_pos := Mem.Col2.DGam_pos (posStar_of_ok hX) R
  dvd i hi x := (card_stab_dvd_autU i x.1 _).trans
    (card_autU_dvd_DGam (posStar_of_ok hX) R (by omega) hi ⟨(twRep i x).deco.2.lat, (twRep i x).deco.2.uni⟩)

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Laws


section Col

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} {G : ChGlob X R.m}

end Col

end Chain

end GlobalTheory.GO
end
end

