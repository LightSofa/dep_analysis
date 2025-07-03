import mobase
from .main import ModDepAnalyzerPlugin


# =============================================================================
# 插件入口点
# =============================================================================
def createPlugin() -> mobase.IPlugin:
    """MO2调用此函数来创建插件实例。"""
    return ModDepAnalyzerPlugin()