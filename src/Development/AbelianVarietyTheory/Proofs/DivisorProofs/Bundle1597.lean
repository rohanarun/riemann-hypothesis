module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Geo Chars)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def EmbCM (Bs : Base D.host.F D.host.E) : Prop := ∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)

def OverH (c : D.host.E) (A : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {n : ℕ}
    (V : Spc D.host.F D.host.E n) : Prop :=
  ∃ h : A.rank = n, V.J = c • Matrix.reindex (finCongr h) (finCongr h) A.gram ∧
    ∀ y, y ∈ V.L ↔ (fun i => star (y (finCongr h i))) ∈ Λ

def OverW (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) {d : ℕ} (Z : Spc D.host.F D.host.E d) : Prop :=
  ∃ h : WW.rank = d, Z.J = D.host.xi0 • Matrix.reindex (finCongr h) (finCongr h) WW.gram.transpose ∧
    ∀ y, y ∈ Z.L ↔ (fun i => y (finCongr h i)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ

def Over {A A' WW : HSp D} (X : Tri T A A' WW) {a a' : ℕ} (Γ : Geo D.sp.cm.sig a a') : Prop :=
  OverH 1 A X.rA.Λ Γ.V ∧ OverH (-1) A' X.rA'.Λ Γ.V' ∧ OverW WW X.rW.Λ Γ.W

def Fit (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t μ₀ : T) (Bs : Base D.host.F D.host.E) (a a' : ℕ) : Prop :=
  GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ Bs.IsGood D.sp.cm.sig ∧ EmbCM Bs ∧ (GlobalTheory.SqStep.chs G i j t).IsGood Bs a a' ∧
    (GlobalTheory.SqStep.chs G i j μ₀).IsGood Bs a a' ∧ ∀ w, ((a + a' : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

theorem OverH.eq {c : D.host.E} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {n : ℕ}
    {V V₂ : Spc D.host.F D.host.E n} (h : OverH c A Λ V) (h₂ : OverH c A Λ V₂) : V₂.J = V.J ∧ V₂.L = V.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem OverW.eq {WW : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} {d : ℕ}
    {Z Z₂ : Spc D.host.F D.host.E d} (h : OverW WW Λ Z) (h₂ : OverW WW Λ Z₂) : Z₂.J = Z.J ∧ Z₂.L = Z.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem Fit.down_left {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {b a' : ℕ}
    (h : Fit G W i j t μ₀ Bs (b + 2) a') : Fit G W i j t μ₀ Bs b a' := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, c.resα, fun x => ?_, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, c₀.resα, fun x => ?_, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resβ x]; simp [pow_add]
  · rw [c₀.resβ x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

theorem Fit.down_right {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a b : ℕ}
    (h : Fit G W i j t μ₀ Bs a (b + 2)) : Fit G W i j t μ₀ Bs a b := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, fun x => ?_, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, fun x => ?_, c₀.resβ, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resα x]; simp [pow_add]
  · rw [c₀.resα x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

end GlobalTheory.SqStepBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open _root_.Formalism.L2.Col

theorem mem_dualFr_span_iff_dualsum {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Fin n → K))
    (φ : Fin n → K) :
    φ ∈ dualFr (Submodule.span (𝓞 K) S) ↔ ∀ x ∈ S, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
    | smul a x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ a hx

theorem dualFr_tauLat_sumLat : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  intro E K ι _ _ _ _ _ emb n N hN M L hL τ
  subst hN
  have hC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => rfl
  have hLst : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have split : ∀ φ x : Fin (n + 1) → K, φ ⬝ᵥ x = (fun k => φ (Fin.castSucc k)) ⬝ᵥ (fun k => x (Fin.castSucc k))
      + φ (Fin.last n) * x (Fin.last n) := by
    intro φ x
    simp only [dotProduct, Fin.sum_univ_castSucc]
  ext φ
  rw [tauLat, mem_dualFr_span_iff_dualsum]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [tauLat, mem_dualFr_span_iff_dualsum]
      rintro _ ⟨m, hm, rfl⟩
      let v : Fin (n + 1) → E := Fin.lastCases 0 m
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 0, ?_⟩
        · simpa [hC, v] using hm
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      simpa [hC, v] using this
    · let v : Fin (n + 1) → E := Pi.single (Fin.last n) 1
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 1, ?_⟩
        · have : (fun k : Fin n => v (Formalism.L2.Col.Br.iC rfl k)) = 0 := by
            funext k; simp [hC, v, Fin.castSucc_ne_last]
          rw [this]; exact M.zero_mem
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      have h0 : (fun k : Fin n => (fun a => emb τ (v a)) (Fin.castSucc k)) = 0 := by
        funext k; simp [v, Fin.castSucc_ne_last]
      rw [h0, dotProduct_zero, zero_add] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      rw [hLst, mul_one]
      have hv1 : (fun (x : Fin (n + 1) → E) a => emb τ (x a)) v (Fin.last n) = 1 := by simp [v]
      rw [hv1, mul_one] at hc
      rw [← hc]
  · rintro ⟨h1, c, hc⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, hL] at hv
    obtain ⟨hvM, d, hd⟩ := hv
    rw [split]
    refine add_mem ?_ ?_
    · rw [tauLat, mem_dualFr_span_iff_dualsum] at h1
      have := h1 _ ⟨_, hvM, rfl⟩
      simpa [hC] using this
    · rw [hLst] at hc hd
      refine Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) d, ?_⟩
      rw [map_mul, hc, mul_one]
      show _ = _ * emb τ (v (Fin.last n))
      rw [← hd]
      rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvNeZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_ne_zero {κ : Type} [Fintype κ] (g : SInf F κ) (hg : g ≠ 0) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra! h
    exact hg (SchwartzMap.ext h)
  have hfin : {v | ¬ φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hstd
  set T := hfin.toFinset with hT
  have hy : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra! h
    exact h0 v (funext h)
  choose y hy using hy
  let xf : κ → Af F := fun i => ⟨fun v => if v ∈ T then y v i else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [if_neg hv]
    exact zero_mem _⟩
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), xf i)
  intro hz
  have hx := congrFun hz x
  have e1 : (fun i => evI F (x i)) = a := funext fun i => by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)
  have e2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ T then y v i else 0 := fun v => funext fun i => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, e1, e2] at hx
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hx
  · rcases mul_eq_zero.1 hx with h | h
    · exact ha h
    · obtain ⟨v, hv, h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [hv, if_true] at h
      exact hy v h
  · intro v hv
    by_contra hvT
    apply hv
    have hφ : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra hc
      exact hvT (hfin.mem_toFinset.2 hc)
    have hvT' : v ∉ T := hvT
    simp only [hvT', if_false, hφ]
    rw [Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) (a := fun _ => 0)
      (fun i => zero_mem _)]
    rfl

theorem exists_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ he
  obtain ⟨ei, ev, hei, hev, hpure⟩ := he.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra! h
    exact hei (ContinuousLinearMap.ext h)
  have hfam : GlobalTheory.BigNZ.Fam M M.vac := ⟨fun v => (hM.vac v).1, Filter.Eventually.of_forall fun _ => rfl⟩
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, hfam.mem hM f, ?_⟩
  rw [hpure f M.vac hfam.1 hfam.2]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.ThK.EvNeZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.KerConjMean

variable (D : D7) (δ t0 : ℂ)

abbrev lat : AddSubgroup ℂ := lamOf D D.host.ccK δ

def fld : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.embLL ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})

theorem embLL_mem (x : D.what₂.LL) : D.what₂.embLL x ∈ fld D δ t0 :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨x, rfl⟩)

def ext (σ : D.what₂.LL →+* ℂ) : Set (fld D δ t0 →ₐ[ℚ] ℂ) :=
  {ρ | ∀ x, ρ ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩ = σ x}


open Classical in
def tc (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℂ :=
  if h : ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) t then h.choose else 0

def hArea (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ := Real.posLog (area (lamConj (fld D δ t0) ρ (lat D δ)))⁻¹

def hTh (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ :=
  Real.posLog (nrm1Sq (lamConj (fld D δ t0) ρ (lat D δ)) (GL3Theta.th0 (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ)))

def avg (σ : D.what₂.LL →+* ℂ) (h : (fld D δ t0 →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ᶠ ρ ∈ ext D δ t0 σ, h ρ) / Nat.card (ext D δ t0 σ)

end GlobalTheory.KerConjMean

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.KerConjMean

open GlobalTheory.SumSize GlobalTheory.RowTest GlobalTheory.FunObj GlobalTheory.ChiGrid Formalism.IndefR.Links Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  (ch : _root_.GlobalTheory.RowTest.Choice R) (C b C1 : ℝ)

def RatTopAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1))), ∀ u,
    ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjTopAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ), nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt)

theorem chrW_chs {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ x = (nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  show GlobalTheory.LFun.locChar (GlobalTheory.SqStep.chs G i j t).ν _ _ = _
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq (chrEq_nu G t i j hL)]

theorem eps_mul_of_condExp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) :
    (ν₀ s : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) =
      (((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀))⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ *
        (((ν₀ * ξ) s : ℂ) * eps ψ (ν₀ * ξ) z) := by
  unfold eps
  rw [h]
  simp only [MonoidHom.mul_apply, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_inv, Units.val_inv_eq_inv_val]
  have h1 : (ξ s : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (ξ (unifAt v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem chs_T_base {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) : (GlobalTheory.SqStep.chs G i j μ₀).T = G.pl.S0 := by
  classical
  have hQ : Lc.Q μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
    have h := (hL.Q_ram μ₀ PP).2 (Or.inl hPP)
    apply h
    rw [hL.xi_base]
    intro x _
    rfl
  have htw : twPl G μ₀ = ∅ := by
    unfold twPl locPl
    rw [hQ, Finset.union_empty]
    exact Finset.filter_false_of_mem fun w hw h => h hw
  show G.pl.S0 ∪ (twPl G μ₀).image _ = _
  rw [htw, Finset.image_empty, Finset.union_empty]

end GlobalTheory.SqStepArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanishStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  first | exact @GlobalTheory.AdelicFourierUniq.eq_zero | exact GlobalTheory.AdelicFourierUniq.eq_zero | (intros; apply GlobalTheory.AdelicFourierUniq.eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwineStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_good_models_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  first | exact @GlobalTheory.EvTame.isTame_of_isEv | exact GlobalTheory.EvTame.isTame_of_isEv | (intros; apply GlobalTheory.EvTame.isTame_of_isEv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  first | exact @GlobalTheory.NormAtPlace.evFin_norm_eq | exact GlobalTheory.NormAtPlace.evFin_norm_eq | (intros; apply GlobalTheory.NormAtPlace.evFin_norm_eq <;> assumption)
end

