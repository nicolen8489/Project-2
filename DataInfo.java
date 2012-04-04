public class DataInfo {
  private int maxSatClause;
  private int localMinCount;
  private int localMinSatClauseSum;
  public DataInfo() {
    maxSatClause = 0;
  }
  public int getMaxSatClause() {
    return maxSatClause;
  }
  public double getAvgLocalMinSatClauses() {
    return (double)localMinCount / localMinSatClauseSum;
  }
}
