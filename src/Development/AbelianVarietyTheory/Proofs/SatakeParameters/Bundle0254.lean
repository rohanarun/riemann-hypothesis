module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentification
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

theorem tau_nonempty' (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

variable {D : D7} {X : Fields} (s : Seam D X)

theorem iE_single {a : ℕ} (j : Fin a) : (fun k => s.iE ((Pi.single j (1 : X.E) : Sp X.E a) k)) = (Pi.single j 1 : Fin a → D.host.E) := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem seamHom_injective {a b : ℕ} : Function.Injective (seamHom s (a := a) (b := b)) := by
  intro x x' h
  refine LinearMap.ext fun v => funext fun l => ?_
  have e1 := seamHom_apply s x (fun k => s.iE.symm (v k)) l
  have e2 := seamHom_apply s x' (fun k => s.iE.symm (v k)) l
  simp only [RingEquiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, h]

theorem seamHom_surjective {a b : ℕ} : Function.Surjective (seamHom s (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' y).map s.iE), ?_⟩
  unfold seamHom
  rw [LinearMap.toMatrix'_toLin']
  have : ((LinearMap.toMatrix' y).map s.iE).map s.iE.symm = LinearMap.toMatrix' y := by
    ext p q; simp
  rw [this, Matrix.toLin'_toMatrix']

theorem embH_seamHom (hs : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE D.host.E a b) :
    embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ) := by
  funext τ i j
  show δ * X.embC s.σ₀ τ (seamHom s x (Pi.single j 1) i) = δ * TaylorLogMetric.embT D (s.iT τ) (x (Pi.single j 1) i)
  congr 1
  show s.σ₀ (X.emb τ _) = _
  rw [hs.1, seamHom_apply, iE_single]

theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι]
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) {a b : ℕ} : Function.Injective (embH emb δ (a := a) (b := b)) := by
  intro x y h
  obtain ⟨τ⟩ := (inferInstance : Nonempty ι)
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (emb τ).injective (mul_left_cancel₀ hδ this)

end GlobalTheory.TwU.SeamEmb

namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

theorem seam_coords : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  intro D X s hs δ a b
  have hemb := embH_seamHom s hs δ (a := a) (b := b)
  have hcomp : ∀ (x : HomE D.host.E a b) (v : VV D.what₂.Tau a b),
      embH (X.embC s.σ₀) δ (seamHom s x) = (fun τ => v (s.iT τ)) ↔ embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
    intro x v
    rw [hemb]
    constructor
    · intro h
      funext σ
      have := congrFun h (s.iT.symm σ)
      simpa using this
    · intro h; rw [h]
  refine ⟨⟨seamHom_injective s, seamHom_surjective s⟩, hemb, ?_, ?_⟩
  · intro M M' hM v
    constructor
    · rintro ⟨y, hy, hyv⟩
      obtain ⟨x, rfl⟩ := seamHom_surjective s y
      exact ⟨x, (hM x).1 hy, (hcomp x v).1 hyv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨seamHom s x, (hM x).2 hx, (hcomp x v).2 hxv⟩
  · intro hδ Ξ v
    haveI : Nonempty D.what₂.Tau := tau_nonempty' D
    haveI : Nonempty X.Tau := ⟨s.iT.symm (Classical.arbitrary _)⟩
    have hex : (∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)) ↔ ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := seamHom_surjective s y
        exact ⟨x, (hcomp x v).1 hy⟩
      · rintro ⟨x, hx⟩
        exact ⟨seamHom s x, (hcomp x v).2 hx⟩
    unfold onV
    by_cases h' : ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v
    · have h := hex.2 h'
      rw [dite_eq_left h, dite_eq_left h']
      congr 1
      apply embH_injective (X.embC s.σ₀) hδ
      rw [h.choose_spec, (hcomp _ v).2 h'.choose_spec]
    · have h : ¬ ∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ) := fun h => h' (hex.1 h)
      rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.TwU.SeamEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepLocalDatumInvariantCosetMove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

variable {E K : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (Psi : Sp E n → K) [Zero K] (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (e e' D : ℕ) (hD : e + e' ≤ D)
    (hInv : ∀ y z : Sp E n, (∀ i, IntAt P ((q ^ e)⁻¹ * z i)) → Psi (y + z) = Psi y)
    (hSupp : ∀ y : Sp E n, Psi y ≠ 0 → ∀ i, IntAt P (q ^ e' * y i))
    (k : Sp E n ≃ₗ[E] Sp E n)
    (hkint : ∀ x : Sp E n, (∀ i, IntAt P (k x i)) → ∀ i, IntAt P (x i))
    (hk : ∀ s l, IntAt P ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)))
    (w w₁ : Sp E n) (hc : ∀ l, IntAt P ((q ^ e)⁻¹ * (k.symm w₁ - w) l)) :
    Psi w₁ = Psi w := by
  by_cases hboth : Psi w₁ = 0 ∧ Psi w = 0
  · rw [hboth.1, hboth.2]
  set u := k.symm w₁ with hu
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)

  have hU : ∀ i, IntAt P (q ^ e' * u i) := by
    by_cases hw : Psi w = 0
    · have hw₁ : Psi w₁ ≠ 0 := fun h => hboth ⟨h, hw⟩
      have h1 := hSupp w₁ hw₁
      have h2 : ∀ i, IntAt P (k (q ^ e' • u) i) := by
        intro i
        rw [map_smul, hu, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
        exact h1 i
      intro i
      have := hkint _ h2 i
      rwa [Pi.smul_apply, smul_eq_mul] at this
    · have h1 := hSupp w hw
      intro i
      have e1 : q ^ e' * u i = q ^ e' * w i + q ^ (e + e') * ((q ^ e)⁻¹ * (u - w) i) := by
        rw [Pi.sub_apply, pow_add]
        field_simp
        ring
      rw [e1]
      exact mem_intS.1 ((intS P).add_mem (mem_intS.2 (h1 i))
        ((intS P).mul_mem (mem_intS.2 (hqpow _)) (mem_intS.2 (hc i))))

  have hz : ∀ l, IntAt P ((q ^ e)⁻¹ * (w₁ - w) l) := by
    intro l
    have hsum : u = ∑ s, u s • (Pi.single s 1 : Sp E n) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hw₁ : w₁ = k u := by rw [hu, LinearEquiv.apply_symm_apply]
    obtain ⟨t, ht⟩ : ∃ t, D = e + e' + t := ⟨D - (e + e'), by omega⟩
    have e2 : (q ^ e)⁻¹ * (w₁ - w) l =
        (∑ s, (q ^ e' * u s) * ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) * q ^ t) +
          (q ^ e)⁻¹ * (u - w) l := by
      have e3 : (w₁ - w) l = (∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) + (u - w) l := by
        have e4 : (k u - u) l = ∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l) := by
          conv_lhs => rw [hsum]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_apply]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smul, ← smul_sub, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        rw [← e4, hw₁]
        simp only [Pi.sub_apply]
        ring
      rw [e3, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ht, pow_add, pow_add]
      field_simp
    rw [e2]
    refine mem_intS.1 ((intS P).add_mem ((intS P).sum_mem fun s _ => ?_) (mem_intS.2 (hc l)))
    exact (intS P).mul_mem ((intS P).mul_mem (mem_intS.2 (hU s)) (mem_intS.2 (hk s l))) (mem_intS.2 (hqpow t))
  have := hInv w (w₁ - w) hz
  rwa [add_sub_cancel] at this

end GlobalTheory.PsiCosetInv

namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := by
  intro X Pr R Ch sel S mu cst L G m2 hL al P x₀ k w w₁ hk hc
  have hInv := hL.psiInv al P x₀
  have hSupp := hL.psiSupp al P x₀
  unfold SameCoset at hc
  have hkint : ∀ x : Sp X.E (R.N (m2 + 1)), (∀ i, IntAt P.1 (k.1 x i)) → ∀ i, IntAt P.1 (x i) := by
    intro x hx
    have h1 : k.1 x ∈ stdAt X.E (R.N (m2 + 1)) P.1 := (mem_localization_standardLattice P.1 _).2 hx
    exact (mem_localization_standardLattice P.1 _).1 ((k.2 x).1 h1)
  have hq := qOf_ne (E := X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := intAt_nat (P := P.1) _
  by_cases hP : P.1 ∈ Pr.vGs
  · simp only [if_pos hP] at hInv hSupp hc
    exact core _ _ hq hqi 0 1 (cst.D P) (by rw [hL.depthG P hP]) hInv hSupp k.1 hkint hk w w₁ hc
  · simp only [if_neg hP] at hInv hSupp hc
    exact core _ _ hq hqi cst.M cst.M (cst.D P) (by have := hL.depthQ P hP; omega) hInv hSupp k.1 hkint hk w w₁ hc

end GlobalTheory.PsiCosetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem smul_sub_mem_of_frames {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Sp E n)} {fr : Frs E n SB} (hf : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr) (P : SB) (s : E) (a b y₀ : Sp E n)
    (ha : ∀ l, IntAt P.1 (s * ((fr P).symm a - y₀) l)) (hb : ∀ l, IntAt P.1 (s * ((fr P).symm b - y₀) l)) :
    s • (a - b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  have h : s • (fr P).symm (a - b) ∈ stdAt E n P.1 := GlobalTheory.TopStep.mem_stdAt.2 fun l => by
    have := GlobalTheory.TopStep.intAt_sub (ha l) (hb l)
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    ring
  have := (hf P _).2 h
  rwa [map_smul, LinearEquiv.apply_symm_apply] at this

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem chartBaseRepresentative_penultimate_step (A : AdData t u μ St) (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ) :
    y0At A (t.m2 + 1) hi β P = A.y0 β P := by
  unfold y0At
  rw [dite_eq_left rfl]

end

theorem cosetOf_eq_yb : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c
  obtain ⟨w, -, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  ext y
  constructor
  · intro hy
    rw [hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_comap]
    have h1 := hy P
    have h2 := H.coset c w hwm P
    rw [chartBaseRepresentative_penultimate_step] at h1
    unfold SameCoset at h1 h2
    have key := smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2
    by_cases hP : P.1 ∈ t.Pr.vGs
    · simp only [hP, if_true] at key ⊢
      simpa using key
    · simp only [hP, if_false] at key ⊢
      simpa [zpow_natCast] using key
  · intro hy P
    rw [chartBaseRepresentative_penultimate_step]
    exact H.coset c y hy P

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralHilbert90DetHostField
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90
open GlobalTheory.AdeleBaseChange
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def evP (P : HeightOneSpectrum (𝓞 E)) : FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun z := z P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem localComponent_apply₂ (P : HeightOneSpectrum (𝓞 E)) (z : FiniteAdeleRing (𝓞 E) E) : evP P z = z P := rfl

theorem localComponent_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    evP P (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (P.adicCompletion E) x := rfl

variable [StarRing E]

end GlobalTheory.TwU.IntegralHilbert90
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_solvable_cm_extension_split_place : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  first | exact @GlobalTheory.AboveL.exists_cm_solvable_split | exact GlobalTheory.AboveL.exists_cm_solvable_split | (intros; apply GlobalTheory.AboveL.exists_cm_solvable_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedResiduesInFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

namespace GlobalTheory.CRTFrame

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) (M : 𝓞 E) (hM : M ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P ((algebraMap (𝓞 E) E M)⁻¹ * algebraMap (𝓞 E) E z) := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {M} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hM
  have hex : ∃ m : ℕ, ¬ I ≤ P.asIdeal ^ m := by
    by_contra h
    push Not at h
    apply hI
    have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
    have := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal hP
    rw [eq_bot_iff, ← this]
    exact le_iInf h
  set m0 := Nat.find hex with hm0
  have hm0pos : m0 ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm0, h0, pow_zero] at this
    exact this (by rw [Ideal.one_eq_top]; exact le_top)
  refine ⟨m0 - 1, ?_⟩
  have hle : I ≤ P.asIdeal ^ (m0 - 1) := by
    have := Nat.find_min hex (show m0 - 1 < m0 by omega)
    push Not at this
    exact this
  have hnle : ¬ I ≤ P.asIdeal ^ (m0 - 1 + 1) := by
    rw [show m0 - 1 + 1 = m0 by omega]; exact Nat.find_spec hex
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hle
  have hQP : ¬ Q ≤ P.asIdeal := by
    intro h
    apply hnle
    rw [hQ, pow_succ]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.mp hQP
  intro z hz
  have hmem : z * s ∈ I := by
    rw [hQ]; exact Ideal.mul_mem_mul hz hsQ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hM' : algebraMap (𝓞 E) E M ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hM
  refine ⟨a, s, hsP, ?_⟩
  have h2 : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E M = algebraMap (𝓞 E) E z * algebraMap (𝓞 E) E s := by
    rw [← map_mul, ← map_mul, ha]
  field_simp
  linear_combination -h2

theorem approx_frames (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ) :
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  classical
  set w : SB → Sp E n := fun P => f P (y0 P) with hwdef
  set c : SB → Fin n → Fin n → E := fun P j l => (f P).symm (Pi.single j 1) l with hcdef
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    ((Finset.univ.image (fun x : SB × Fin n × Fin n => c x.1 x.2.1 x.2.2)) ∪
      (Finset.univ.image (fun x : SB × Fin n => w x.1 x.2)))
  set D : 𝓞 E := (b : 𝓞 E) with hDdef
  have hD : D ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hc : ∀ P j l, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * c P j l := by
    intro P j l
    obtain ⟨r, hr⟩ := hb (c P j l) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(P, j, l), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  have hw : ∀ P j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * w P j := by
    intro P j
    obtain ⟨r, hr⟩ := hb (w P j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(P, j), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose cr hcr using hc
  choose wr hwr using hw
  have hN : ∀ P : SB, ((qOf P.1 : ℕ) : 𝓞 E) ≠ 0 := by
    intro P
    rw [Ne, Nat.cast_eq_zero]
    show Ideal.absNorm P.1.asIdeal ≠ 0
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  set M : SB → 𝓞 E := fun P => ((qOf P.1 : ℕ) : 𝓞 E) ^ (e P) * D * D with hMdef
  have hM : ∀ P, M P ≠ 0 := fun P => mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hN P)) hD) hD
  choose k hk using fun P : SB => exists_pow_intAt_div P.1 (M P) (hM P)
  set kk : HeightOneSpectrum (𝓞 E) → ℕ := fun P => if h : P ∈ SB then k ⟨P, h⟩ else 0 with hkkdef
  have crt : ∀ j : Fin n, ∃ z : 𝓞 E, ∀ (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ SB),
      z - wr ⟨P, hP⟩ j ∈ P.asIdeal ^ kk P := fun j =>
    IsDedekindDomain.exists_forall_sub_mem_ideal (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) kk
      (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun P => wr P j)
  choose z hz using crt
  have hD' : algebraMap (𝓞 E) E D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hD
  refine ⟨fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j), ?_⟩
  intro P l
  have hexp : ∀ v : Sp E n, (f P).symm v l = ∑ j, v j * c P j l := by
    intro v
    have hv : v = ∑ j, v j • (Pi.single j 1 : Sp E n) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply, c]
  have hmem : (∑ j, (z j - wr P j) * cr P j l) ∈ P.1.asIdeal ^ k P := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    have := hz j P.1 P.2
    simpa [kk, P.2] using this
  have key := hk P _ hmem
  convert key using 1
  have h1 : (f P).symm (fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - y0 P
      = (f P).symm ((fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - w P) := by
    rw [map_sub]; simp [w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hexp, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := hcr P j l
  have e2 := hwr P j
  simp only [M, map_mul, map_sub, map_pow, map_natCast, Pi.sub_apply]
  rw [e1, e2]
  have hq : ((qOf P.1 : ℕ) : E) ≠ 0 := by
    have := hN P
    intro h; apply this
    exact (IsFractionRing.injective (𝓞 E) E) (by rw [map_natCast, h, map_zero])
  field_simp

theorem approx_frames_target : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) :=
  fun E _ _ n SB f y0 e => approx_frames E n SB f y0 e

end GlobalTheory.CRTFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldIsoMatrixCongruenceAutomorphismCongruenceStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence : ∀ {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ) (g : Sp X.E N ≃ₗ[X.E] Sp X.E N), (∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ * (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) → ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  first | exact @GlobalTheory.SeamCong.cong_seam | exact GlobalTheory.SeamCong.cong_seam | (intros; apply GlobalTheory.SeamCong.cong_seam <;> assumption)
end

