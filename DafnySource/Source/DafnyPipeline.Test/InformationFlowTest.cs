using System;
using System.Text;
using Xunit;
using Xunit.Abstractions;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using System.Reflection;
using DafnyPipeline;
using Microsoft.VisualStudio.TestPlatform.PlatformAbstractions;
using System.IO;
using System.Linq;
using System.Diagnostics;

namespace DafnyPipeline.Test {
  public class InformationFlowTest {

    private readonly ITestOutputHelper output;

    public InformationFlowTest(ITestOutputHelper output) {
      this.output = output;
    }

    string GetDiff(string expected, string actual) {
      var diff = InlineDiffBuilder.Diff(expected, actual);
      var result = new StringBuilder();
      foreach (var line in diff.Lines) {
        switch (line.Type) {
          case ChangeType.Inserted:
            result.Append("+ ");
            result.AppendLine(line.Text);
            break;
          case ChangeType.Deleted:
            result.Append("- ");
            result.AppendLine(line.Text);
            break;
        }
      }

      return result.ToString();
    }

    public static readonly string dafnyDirectory;
    private static string DafnyDriverProjectFile => Path.Combine(dafnyDirectory, "Source", "DafnyDriver", "DafnyDriver.csproj");
    private static string DefaultDafnyArgs => $"run --no-build --project {DafnyDriverProjectFile} -- -useBaseNameForFileName -countVerificationErrors:0 -compileVerbose:0 /errorTrace:0";

    static InformationFlowTest() {
      var testAssemblyPath = Assembly.GetAssembly(typeof(VerificationStability)).GetAssemblyLocation();
      var parts = testAssemblyPath.Split(Path.DirectorySeparatorChar);
      // This way of finding the repository root is not reliable, we should instead reference the DafnyPipeline assembly and run Dafny in the same process as the unit tests.
      var sourceIndex = Array.FindIndex(parts, e => e == "Source");
      dafnyDirectory = Path.Combine(Path.GetPathRoot(testAssemblyPath)!, Path.Combine(parts.Take(sourceIndex).ToArray()));
      Console.WriteLine("dafnyDirectory: " + dafnyDirectory);
      Console.WriteLine("DafnyDriverProjectFile: " + DafnyDriverProjectFile);
    }

    [Theory]
    [InlineData("empty")]
    [InlineData("injectPolicy")]
    public void testInitFile(string fileName) {
      var testDir = Path.Combine(dafnyDirectory, "Source", "DafnyInfoFlowTest", "testFiles/");
      var stdOut = runFile(testDir + fileName + ".dfy");
      output.WriteLine(stdOut);
      var diff = GetDiff(File.ReadAllText(testDir + fileName + "Expect.dfy"), File.ReadAllText(testDir + fileName + ".if.dfy"));
      var expectedDiff = "";
      Assert.Equal(expectedDiff, diff);
    }

    [Fact]
    public void testUnchangedAfterInitTwice() {
      var testDir = Path.Combine(dafnyDirectory, "Source", "DafnyInfoFlowTest", "testFiles/");
      var stdOut1 = runFile(testDir + "initTwice.dfy");
      output.WriteLine(stdOut1);
      var stdOut2 = runFile(testDir + "initTwice.dfy");
      output.WriteLine(stdOut2);
      var diff = GetDiff(File.ReadAllText(testDir + "initTwiceExpect.dfy"), File.ReadAllText(testDir + "initTwice.if.dfy"));
      var expectedDiff = "";
      Assert.Equal(expectedDiff, diff);
    }

    public string runFile(string fileName) {
      var fileNoExt = fileName.Remove(fileName.Length - 4);
      var processStartInfo = new ProcessStartInfo {
        FileName = "dotnet",
        Arguments = $"{DefaultDafnyArgs} /compile:0 /env:0 -dprint:{fileNoExt}.if.dfy -printVerifiedProceduresCount:0 -infoFlow:1 {fileName}",
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false
      };

      using var dafnyProcess = Process.Start(processStartInfo);
      var result = dafnyProcess.StandardOutput.ReadToEnd();
      dafnyProcess.WaitForExit();
      

      if (dafnyProcess.ExitCode != 0) {
        output.WriteLine("Arguments:", processStartInfo.Arguments);
        output.WriteLine("Result:");
        output.WriteLine(result);
        output.WriteLine(dafnyProcess.StandardError.ReadToEnd());
        Console.Out.Flush();
      }
      Assert.Equal(0, dafnyProcess.ExitCode);
      dafnyProcess.Dispose();
      return result;
    }

  }
}
