module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.Columns.HeckeSp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD
open scoped TensorProduct

namespace GlobalTheory.WH

section Wd

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

def wd (w : ι → Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun t => ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • (w i ∘ₗ LinearMap.proj (t.erase i))

def acx (A : Finset ι → Submodule k E) (w : ι → Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => if (s.card : ℤ) = n then A s else ⊥, wd w⟩

def cupE {E' E'' : Type} [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'')
    (a : Finset ι → E) (b : Finset ι → E') : Finset ι → E'' := fun u =>
  ∑ j ∈ u, μ (a (u.filter (· ≤ j))) (b (u.filter (j ≤ ·)))

end Wd

section Join

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

def lft (s : Finset (ι ⊕ₗ κ)) : Finset ι := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toLeft

def rgt (s : Finset (ι ⊕ₗ κ)) : Finset κ := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toRight

def uni (I : Finset ι) (J : Finset κ) : Finset (ι ⊕ₗ κ) := (I.disjSum J).map (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding

variable {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

def join (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset (ι ⊕ₗ κ) → E'' :=
  fun s => μ (a (lft s)) (b (rgt s))

def edge1 (a : Finset ι → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (rgt s).card = 1 then a (lft s) else 0

def edge2 (b : Finset κ → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (lft s).card = 1 then b (rgt s) else 0

def mixF (A : Finset ι → Finset κ → Submodule k E) (s : Finset (ι ⊕ₗ κ)) : Submodule k E :=
  if (lft s).Nonempty ∧ (rgt s).Nonempty then A (lft s) (rgt s) else ⊥

end Join

section Koszul

variable {k : Type} [Field k] {σ : Type} [LinearOrder σ] {E : Type} [AddCommGroup E] [Module k E]

end Koszul

section Forms

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def XZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.rTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def actZ : K ⊗[ℂ] K →ₐ[ℂ] Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K)))

def MZ (a : ℕ) (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  Submodule.map₂ (TensorProduct.mk ℂ _ _) (omB ℂ K (rB ℂ K x I) (d - a)) (omB ℂ K (rB ℂ K x J) a)

def ctr (τ : DR ℂ K →ₗ[K] K) (w : DR ℂ K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ ((Algebra.linearMap F K).restrictScalars ℂ ∘ₗ
    (Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ ∘ₗ LinearMap.mulLeft ℂ w))

end Forms

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ}

def pr2L (j2 : K →ₐ[ℂ] K') : DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  (GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ

def R2 (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  (integralClosure ((rB ℂ K x J).map j2) K').restrictScalars ℂ

variable [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def RY (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  rB ℂ K' x I ⊔ R2 x j2 J

def gY (j2 : K →ₐ[ℂ] K') : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  TensorProduct.lift ((LinearMap.mul ℂ (DR ℂ K')).compl₁₂ ((GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ) (pr2L j2))

def Val (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (v : K') (c : ℂ) : Prop :=
  ∃ (b : K') (hb : b ∈ B) (hbv : b * v ∈ B), e ⟨b, hb⟩ ≠ 0 ∧ e ⟨b * v, hbv⟩ = e ⟨b, hb⟩ * c

def IsFix (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (j2 : K →ₐ[ℂ] K') (B0 : Subalgebra ℂ K) : Prop :=
  ∀ b ∈ B0, ∀ h1 : algebraMap K K' b ∈ B, Val B e (j2 b) (e ⟨_, h1⟩)

end Y

end GlobalTheory.WH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
section
noncomputable section

namespace GlobalTheory.GO

open NumberField _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

section Exp

open MvPolynomial Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Exp

namespace ChSrc

open Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {X : Fields} {R : Ranks} (σ : X.K →+* ℂ)

theorem jetInVV_trueWt (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) : JetInVV X.K (trueWt hc i) (trueWt hc (i + 1)) (nuEnd hc i) := by
  have hab : R.N i < R.N (i + 1) := by
    simp only [Ranks.N]
    nlinarith
  have hW : WtCompat hab (trueWt hc i) (trueWt hc (i + 1)) (sD hc i) (sS hc i) (nuEnd hc i) := by
    refine ⟨fun τ a => ?_, fun τ j hj => trueWt_new hc hi τ j (by omega), fun τ => nuEnd_cast hc hi τ⟩
    have h1 := trueWt_old hc hi τ (Fin.castLE hab.le a) (by simp)
    simp only [Fin.coe_castLE] at h1
    rw [h1]
    ring
  haveI : Infinite X.K := Infinite.of_injective (Nat.cast : ℕ → X.K) Nat.cast_injective
  intro J P hP
  exact GlobalTheory.JetPoint.jetMap_mem hab.le (nuEnd hc i) P _
    (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem X.K X.Tau _ _ hab _ _ _ _ _ hW ap P hP) J

end ChSrc

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def labIn (n : ℕ) (s : List ℕ) : List ℤ :=
  s.map (fun a => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a => -(a : ℤ))

def IsLabElt (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E) (α : GA D V), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ α ∈ GfC V ∧
    (x : GL _ _) = finHom V α ∧ SuppF V f α ∧ DivAt V e (ϖ : D.host.E) d α

def IsLocElt (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (g : GA D V), IsPrimeIdem P e f ∧ g ∈ GfC V ∧ (x : GL _ _) = finHom V g ∧ SuppF V f g

def SphOp (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  Hecke₂ V (KsphC V ∅) (fun _ => 1) ∅ P d R

def IsLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop := ∃ R, SphOp V P d R


open Classical in
def rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Finset (GA D V) :=
  if h : IsLab V P d then h.choose else ∅

def hyp (V : HSp D) (P : Pl D.host.E) : Set (GA D V) :=
  {k | k ∈ KsphC V ∅ ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f k}

def opOf {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (c : List ℤ →₀ ℂ) : Module.End ℂ M :=
  c.sum fun d z => z • ∑ γ ∈ rep V P d, π γ

def hk (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  c.sum fun d z => z • heckeLin V (rep V P d)

def hkF (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : Bridge.Gf V → W) :
    Bridge.Gf V → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ rep V P d, F (h * (finHom V).rangeRestrict γ)

def dualC (c : List ℤ →₀ ℂ) : List ℤ →₀ ℂ := Finsupp.mapDomain dualLab c


open Classical in
def evC (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  c.sum fun d z => if IsLab V P d then z * a d else 0

def splitC (n : ℕ) (z : ℕ → ℂ) : List ℤ →₀ ℂ := ∑ j ∈ Finset.range (n + 1), Finsupp.single (splitLab n j) (z j)

def UnrPl (P : Pl D.host.E) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ e f, IsPrimeIdem P e f → ∀ x : (AE D)ˣ, f * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ e f', IsPrimeIdem P e f' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True),
    IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f

section Pair

variable (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E)

def VacFix : Prop := ∀ f, IsVacAt ψ S T P f → ∀ k ∈ hyp S P, ∀ k' ∈ hyp T P, om (k, k') f = f

def Match (cS cT : List ℤ →₀ ℂ) : Prop :=
  ∀ f, IsVacAt ψ S T P f →
    opOf (om.comp (MonoidHom.inl _ _)) P cS f = opOf (om.comp (MonoidHom.inr _ _)) P cT f

def SphCorr : Prop :=
  VacFix ψ om P ∧ (∀ cT, ∃ cS, Match ψ om P cS cT) ∧ ∀ cS, ∃ cT, Match ψ om P cS cT

end Pair

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Core (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

variable (R : RealDat D A Ks)

def Good (t : T) (P : Pl D.host.E) : Prop := ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P

def IsSF (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ SF ↔ ∃ PP ∈ R.Pg, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def FixAll (t : T) (P : Pl D.host.E) : Prop :=
  (∀ k, k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P) ∧ VacFix R.ψ (R.ωX t) P ∧ ∀ i, VacFix R.ψ (R.ωP i t) P

def SchurAll : Prop :=
  (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))
    (R.νY t j) (R.fdY t j)) ∧
  SchurMult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0 ∧
  ∀ i, SchurMult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i)

def MatchE (t : T) (P : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) →
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c0) (R.HE.e (R.Th t y))

def MatchW (i : Fin D.R.m) (t : T) (P : Pl D.host.E) (cV cW : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HV i t).H, (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y) →
    (R.HW i (sg0 D A)).e (R.thG i t y') = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) ((R.HW i (sg0 D A)).e (R.thG i t y))

def TwoSided (t : T) (P : Pl D.host.E) : Prop :=
  ((∀ cX, ∃ c0, MatchE R t P cX c0) ∧ ∀ c0, ∃ cX, MatchE R t P cX c0) ∧
    ∀ i, (∀ cV, ∃ cW, MatchW R i t P cV cW) ∧ ∀ cW, ∃ cV, MatchW R i t P cV cW

def EEc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF c).comap R.HE.e

def Wcc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap
      (R.HW i _).e

def eH (i : Fin D.R.m) : Module.End ℂ (R.HW i (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g

def IsOpsE (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e x)

def IsOpsW (i : Fin D.R.m) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HW i (sg0 D A)).H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, (R.HW i _).e (h P c x) = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P c) ((R.HW i _).e x)

def IsOpsX (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HX t).e (h P c x) = hkF D.sp.X' P c ((R.HX t).e x)

def IsOpsV (i : Fin D.R.m) (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HV i t).e (h P c x) = hkF (Vc D i) P c ((R.HV i t).e x)

def NormalFam {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ok : Pl D.host.E → Prop)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H) : Prop :=
  (∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c')) ∧
    ∀ P, ok P → ∀ c, LinearMap.adjoint (h P c) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c))

end Real

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def locH (σ : L →+* L) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : L :=
  δ * Matrix.trace (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * x)

structure LocPair (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M) : Prop where
  unr : Formalism.UG.IsUnramInv ϖ σ q
  odd : Odd q
  intS : JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)
  intT : JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)
  hermS : ∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i
  hermT : ∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i
  delta : Valued.v δ = 1 ∧ σ δ = -δ
  psi_int : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1
  psi_ne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1
  rho_zero : ρ 0 = 1
  rho_mul : ∀ x y, ρ x * ρ y = ψ ((locH σ δ JS JT x y + σ (locH σ δ JS JT x y)) / 2) • ρ (x + y)
  span : Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧ w = ρ x s} = ⊤
  norm : ∀ g h x, ω (g, h) * ρ x =
    ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * ω (g, h)
  fix : ∀ (g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) (h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    ∀ s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) → ω (g, h) s = s

def LocVac {n n' : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (s : M) : Prop :=
  ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s

end Local

end GlobalTheory.Hk3

end
end

